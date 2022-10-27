{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}

module Keelung.Compiler.Interpret.Kinded (run, runAndCheck, FreeVar, Interpret) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Semiring (Semiring (..))
import Keelung hiding (inputs, interpret, run)
import Keelung.Compiler.Util
import Keelung.Types
import Keelung.Syntax.VarCounters
import Data.Bits (Bits(..))

--------------------------------------------------------------------------------

-- | Interpret a program with inputs.
run' :: (FreeVar t, Interpret t n, GaloisField n, Integral n) => Elaborated t -> [n] -> Either (InterpretError n) ([n], Witness n)
run' elab inputs = runM elab inputs $ do
  let (Elaborated expr comp) = elab
  -- interpret the assignments first
  -- reverse the list assignments so that "simple values" are binded first
  -- see issue#3: https://github.com/btq-ag/keelung-compiler/issues/3
  let numAssignments = reverse (compNumAsgns comp)
  forM_ numAssignments $ \(NumAssignment var e) -> do
    values <- interpret e
    addBinding var values

  let boolAssignments = reverse (compBoolAsgns comp)
  forM_ boolAssignments $ \(BoolAssignment var e) -> do
    values <- interpret e
    addBinding var values

  -- interpret the assertions next
  -- throw error if any assertion fails
  forM_ (compAssertions comp) $ \e -> do
    values <- interpret e
    when (values /= [1]) $ do
      -- collect variables and their bindings in the expression
      vars <- freeVars e
      bindings' <- mapM (\var -> (var,) <$> lookupVar var) $ IntSet.toList vars
      throwError $ InterpretAssertionError e (IntMap.fromList bindings')

  -- lastly interpret the expression and return the result
  interpret expr

-- | Interpret a program with inputs.
run :: (FreeVar t, Interpret t n, GaloisField n, Integral n) => Elaborated t -> [n] -> Either (InterpretError n) [n]
run elab inputs = fst <$> run' elab inputs

-- | Interpret a program with inputs and run some additional checks.
runAndCheck :: (FreeVar t, Interpret t n, GaloisField n, Integral n) => Elaborated t -> [n] -> Either (InterpretError n) [n]
runAndCheck elab inputs = do
  (output, witness) <- run' elab inputs

  -- See if input size is valid
  let (Elaborated _ comp) = elab
  let expectedInputSize = inputVarSize (compVarCounters comp)
  let actualInputSize = length inputs
  when (expectedInputSize /= actualInputSize) $ do
    throwError $ InterpretInputSizeError expectedInputSize actualInputSize

  -- See if free variables of the program and the witness are the same
  variables <- fst <$> runM elab inputs (freeVars elab)
  let varsInWitness = IntMap.keysSet witness
  when (variables /= varsInWitness) $ do
    let missingInWitness = variables IntSet.\\ varsInWitness
    let missingInProgram = IntMap.withoutKeys witness variables
    throwError $ InterpretVarUnassignedError missingInWitness missingInProgram

  return output

--------------------------------------------------------------------------------

-- | For collecting free variables (excluding input variables).
class FreeVar a where
  freeVars :: a -> M n IntSet

instance FreeVar Number where
  freeVars expr = case expr of
    Integer _ -> return mempty
    Rational _ -> return mempty
    NumVar var -> return $ IntSet.singleton var
    NumInputVar _ -> return mempty
    Add x y -> (<>) <$> freeVars x <*> freeVars y
    Sub x y -> (<>) <$> freeVars x <*> freeVars y
    Mul x y -> (<>) <$> freeVars x <*> freeVars y
    Div x y -> (<>) <$> freeVars x <*> freeVars y
    IfNum x y z -> (<>) <$> freeVars x <*> ((<>) <$> freeVars y <*> freeVars z)
    ToNum x -> freeVars x

instance FreeVar Boolean where
  freeVars expr = case expr of
    Boolean _ -> return mempty
    BoolVar var -> return $ IntSet.singleton var
    BoolInputVar _ -> return mempty
    NumBit x _ -> freeVars x
    Eq x y -> (<>) <$> freeVars x <*> freeVars y
    And x y -> (<>) <$> freeVars x <*> freeVars y
    Or x y -> (<>) <$> freeVars x <*> freeVars y
    Xor x y -> (<>) <$> freeVars x <*> freeVars y
    BEq x y -> (<>) <$> freeVars x <*> freeVars y
    IfBool x y z -> (<>) <$> freeVars x <*> ((<>) <$> freeVars y <*> freeVars z)

instance FreeVar () where
  freeVars expr = case expr of
    () -> return mempty

instance FreeVar t => FreeVar (Arr t) where
  freeVars expr = case expr of
    Arr xs -> IntSet.unions <$> mapM freeVars xs

instance FreeVar t => FreeVar (ArrM t) where
  freeVars expr = case expr of
    ArrayRef _ _ addr -> freeVarsOfArray addr
    where
      freeVarsOfArray :: Addr -> M n IntSet
      freeVarsOfArray addr = do
        heap <- asks snd
        case IntMap.lookup addr heap of
          Nothing -> throwError $ InterpretUnboundAddrError addr heap
          Just (elemType, array) -> case elemType of
            NumElem -> return $ IntSet.fromList (IntMap.elems array)
            BoolElem -> return $ IntSet.fromList (IntMap.elems array)
            (ArrElem _ _) -> IntSet.unions <$> mapM freeVarsOfArray (IntMap.elems array)

-- | Collect free variables of an elaborated program (excluding input variables).
instance FreeVar t => FreeVar (Elaborated t) where
  freeVars (Elaborated value comp) = do
    inOutputValue <- freeVars value
    inNumBindings <- forM (compNumAsgns comp) $ \(NumAssignment var val) -> do
      -- collect both the var and its value
      IntSet.insert var <$> freeVars val
    inBoolBindings <- forM (compBoolAsgns comp) $ \(BoolAssignment var val) -> do
      -- collect both the var and its value
      IntSet.insert var <$> freeVars val
    return $
      inOutputValue
        <> IntSet.unions inNumBindings
        <> IntSet.unions inBoolBindings

--------------------------------------------------------------------------------

-- | The interpreter typeclass
class Interpret a n where
  interpret :: a -> M n [n]

instance GaloisField n => Interpret Integer n where
  interpret x = return [fromIntegral x]

instance GaloisField n => Interpret Rational n where
  interpret x = return [fromRational x]

instance GaloisField n => Interpret Bool n where
  interpret True = return [one]
  interpret False = return [zero]

instance (GaloisField n, Integral n) => Interpret Number n where
  interpret val = case val of
    Integer n -> interpret n
    Rational n -> interpret n
    NumVar var -> pure <$> lookupVar var
    NumInputVar var -> pure <$> lookupInputVar var
    Add x y -> zipWith (+) <$> interpret x <*> interpret y
    Sub x y -> zipWith (-) <$> interpret x <*> interpret y
    Mul x y -> zipWith (*) <$> interpret x <*> interpret y
    Div x y -> zipWith (/) <$> interpret x <*> interpret y
    IfNum p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
    ToNum x -> interpret x

instance (GaloisField n, Integral n) => Interpret Boolean n where
  interpret val = case val of
    Boolean b -> interpret b
    BoolVar var -> pure <$> lookupVar var
    BoolInputVar var -> pure <$> lookupInputVar var
    NumBit x i -> do
      xs <- interpret x 
      if testBit (toInteger (head xs)) i
        then return [one]
        else return [zero]
    Eq x y -> do
      x' <- interpret x
      y' <- interpret y
      interpret (x' == y')
    And x y -> zipWith (*) <$> interpret x <*> interpret y
    Or x y -> zipWith (+) <$> interpret x <*> interpret y
    Xor x y -> zipWith (\x' y' -> x' + y' - 2 * (x' * y')) <$> interpret x <*> interpret y
    BEq x y -> do
      x' <- interpret x
      y' <- interpret y
      interpret (x' == y')
    IfBool p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
   
instance GaloisField n => Interpret () n where
  interpret val = case val of
    () -> return []

instance (Interpret t n, GaloisField n) => Interpret (Arr t) n where
  interpret val = case val of
    Arr xs -> concat <$> mapM interpret xs

instance (Interpret t n, GaloisField n) => Interpret (ArrM t) n where
  interpret val = case val of
    ArrayRef _ _ addr -> lookupAddr addr

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = ReaderT (IntMap n, Heap) (StateT (Witness n) (Except (InterpretError n)))

runM :: Elaborated t -> [n] -> M n a -> Either (InterpretError n) (a, Witness n)
runM elab inputs p = runExcept (runStateT (runReaderT p (inputBindings, heap)) mempty)
  where
    (Elaborated _ comp) = elab
    heap = compHeap comp
    inputBindings = IntMap.fromDistinctAscList $ zip [0 ..] inputs

lookupVar :: Show n => Int -> M n n
lookupVar var = do
  bindings <- get
  case IntMap.lookup var bindings of
    Nothing -> throwError $ InterpretUnboundVarError var bindings
    Just val -> return val

lookupInputVar :: Show n => Int -> M n n
lookupInputVar var = do
  bindings <- asks fst
  case IntMap.lookup var bindings of
    Nothing -> throwError $ InterpretUnboundInputVarError var bindings
    Just val -> return val

lookupAddr :: Show n => Int -> M n [n]
lookupAddr addr = do
  heap <- asks snd
  case IntMap.lookup addr heap of
    Nothing -> throwError $ InterpretUnboundAddrError addr heap
    Just (elemType, array) -> case elemType of
      NumElem -> mapM lookupVar (IntMap.elems array)
      BoolElem -> mapM lookupVar (IntMap.elems array)
      (ArrElem _ _) -> concat <$> mapM lookupAddr (IntMap.elems array)

addBinding :: Var -> [n] -> M n ()
addBinding var [val] = modify (IntMap.insert var val)
addBinding _ _ = error "addBinding: expected a single value"

-- addBinding (NumVar var) [val] = modify (IntMap.insert var val)
-- addBinding (ArrayRef _ _ addr) vals = do
--   vars <- collectVarsFromAddr addr
--   mapM_
--     (modify . uncurry IntMap.insert)
--     (zip vars vals)
--   where
--     collectVarsFromAddr :: Addr -> M n [Var]
--     collectVarsFromAddr address = do
--       heap <- asks snd
--       case IntMap.lookup address heap of
--         Nothing -> throwError $ InterpretUnboundAddrError addr heap
--         Just (elemType, array) -> case elemType of
--           NumElem -> return $ IntMap.elems array
--           BoolElem -> return $ IntMap.elems array
--           (ArrElem _ _) -> concat <$> mapM collectVarsFromAddr (IntMap.elems array)
-- addBinding _ _ = error "addBinding: too many values"

--------------------------------------------------------------------------------

data InterpretError n
  = InterpretUnboundVarError Var (Witness n)
  | InterpretUnboundInputVarError Var (IntMap n)
  | InterpretUnboundAddrError Addr Heap
  | InterpretAssertionError Boolean (Witness n)
  | InterpretVarUnassignedError IntSet (Witness n)
  | InterpretInputSizeError Int Int
  deriving (Eq)

instance (GaloisField n, Integral n) => Show (InterpretError n) where
  show (InterpretUnboundVarError var bindings) =
    "unbound variable " ++ show var
      ++ " in bindings "
      ++ showWitness bindings
  show (InterpretUnboundInputVarError var inputs) =
    "unbound input variable " ++ show var
      ++ " in inputs "
      ++ showWitness inputs
  show (InterpretUnboundAddrError var heap) =
    "unbound address " ++ show var
      ++ " in heap "
      ++ show heap
  show (InterpretAssertionError val bindings) =
    "assertion failed: " ++ show val
      ++ "\nbindings of variables: "
      ++ showWitness bindings
  show (InterpretVarUnassignedError missingInWitness missingInProgram) =
    ( if IntSet.null missingInWitness
        then ""
        else
          "these variables have no bindings:\n  "
            ++ show (IntSet.toList missingInWitness)
    )
      <> if IntMap.null missingInProgram
        then ""
        else
          "these bindings are not in the program:\n  "
            ++ showWitness missingInProgram
  show (InterpretInputSizeError expected actual) =
    "expecting " ++ show expected ++ " inputs but got " ++ show actual
      ++ " inputs"
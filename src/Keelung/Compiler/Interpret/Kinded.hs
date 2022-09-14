{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}

module Keelung.Compiler.Interpret.Kinded (run, runAndCheck) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Semiring (Semiring (..))
import Keelung hiding (inputs, interpret)
import Keelung.Compiler.Util
import Keelung.Types

--------------------------------------------------------------------------------

-- | Interpret a program with inputs.
run' :: GaloisField n => Elaborated t -> [n] -> Either (InterpretError n) ([n], Witness n)
run' elab inputs = runMWithInputs elab inputs $ do
  let comp = elabComp elab
  -- interpret the assignments first
  -- reverse the list assignments so that "simple values" are binded first
  -- see issue#3: https://github.com/btq-ag/keelung-compiler/issues/3
  let numAssignments = reverse (compNumAsgns comp)
  forM_ numAssignments $ \(Assignment var e) -> do
    values <- interpret e
    addBinding var values

  let boolAssignments = reverse (compBoolAsgns comp)
  forM_ boolAssignments $ \(Assignment var e) -> do
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
  interpret (elabVal elab)

-- | Interpret a program with inputs.
run :: GaloisField n => Elaborated t -> [n] -> Either (InterpretError n) [n]
run elab inputs = fst <$> run' elab inputs

-- | Interpret a program with inputs and run some additional checks.
runAndCheck :: GaloisField n => Elaborated t -> [n] -> Either (InterpretError n) [n]
runAndCheck elab inputs = do
  (output, witness) <- run' elab inputs

  -- See if input size is valid
  let expectedInputSize = IntSet.size (compInputVars (elabComp elab))
  let actualInputSize = length inputs
  when (expectedInputSize /= actualInputSize) $ do
    throwError $ InterpretInputSizeError expectedInputSize actualInputSize

  -- See if free variables of the program and the witness are the same
  variables <- fst <$> runMWithInputs elab inputs (freeVarsOfElab elab)
  let varsInWitness = IntMap.keysSet witness
  when (variables /= varsInWitness) $ do
    let missingInWitness = variables IntSet.\\ varsInWitness
    let missingInProgram = IntMap.withoutKeys witness variables
    throwError $ InterpretVarUnassignedError missingInWitness missingInProgram

  return output

--------------------------------------------------------------------------------

-- collect free variables of an expression
freeVars :: Val t -> M n IntSet
freeVars expr = case expr of
  Integer _ -> return mempty
  Rational _ -> return mempty
  Boolean _ -> return mempty
  UnitVal -> return mempty
  ArrayVal xs -> IntSet.unions <$> mapM freeVars xs
  Ref (NumVar n) -> return $ IntSet.singleton n
  Ref (BoolVar n) -> return $ IntSet.singleton n
  Ref (ArrayRef _ _ addr) -> freeVarsOfArray addr
  Add x y -> (<>) <$> freeVars x <*> freeVars y
  Sub x y -> (<>) <$> freeVars x <*> freeVars y
  Mul x y -> (<>) <$> freeVars x <*> freeVars y
  Div x y -> (<>) <$> freeVars x <*> freeVars y
  Eq x y -> (<>) <$> freeVars x <*> freeVars y
  And x y -> (<>) <$> freeVars x <*> freeVars y
  Or x y -> (<>) <$> freeVars x <*> freeVars y
  Xor x y -> (<>) <$> freeVars x <*> freeVars y
  BEq x y -> (<>) <$> freeVars x <*> freeVars y
  IfNum x y z -> (<>) <$> freeVars x <*> ((<>) <$> freeVars y <*> freeVars z)
  IfBool x y z -> (<>) <$> freeVars x <*> ((<>) <$> freeVars y <*> freeVars z)
  ToBool x -> freeVars x
  ToNum x -> freeVars x
  where
    freeVarsOfArray :: Addr -> M n IntSet
    freeVarsOfArray addr = do
      heap <- ask
      case IntMap.lookup addr heap of
        Nothing -> throwError $ InterpretUnboundAddrError addr heap
        Just (elemType, array) -> case elemType of
          NumElem -> return $ IntSet.fromList (IntMap.elems array)
          BoolElem -> return $ IntSet.fromList (IntMap.elems array)
          (ArrElem _ _) -> IntSet.unions <$> mapM freeVarsOfArray (IntMap.elems array)

-- | Collect free variables of an elaborated program (that should also be present in the witness)
freeVarsOfElab :: Elaborated t -> M n IntSet
freeVarsOfElab (Elaborated value comp) = do
  inOutputValue <- freeVars value

  let inputBindings = compInputVars comp

  inNumBindings <- forM (compNumAsgns comp) $ \(Assignment (NumVar var) val) -> do
    -- collect both the var and its value
    IntSet.insert var <$> freeVars val
  inBoolBindings <- forM (compBoolAsgns comp) $ \(Assignment (BoolVar var) val) -> do
    -- collect both the var and its value
    IntSet.insert var <$> freeVars val
  return $
    inputBindings
      <> inOutputValue
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

instance GaloisField n => Interpret (Ref t) n where
  interpret (BoolVar var) = pure <$> lookupVar var
  interpret (NumVar var) = pure <$> lookupVar var
  interpret (ArrayRef _ _ addr) = lookupAddr addr

instance GaloisField n => Interpret (Val t) n where
  interpret val = case val of
    Integer n -> interpret n
    Rational n -> interpret n
    Boolean b -> interpret b
    UnitVal -> return []
    ArrayVal xs -> concat <$> mapM interpret xs
    Ref ref -> interpret ref
    Add x y -> zipWith (+) <$> interpret x <*> interpret y
    Sub x y -> zipWith (-) <$> interpret x <*> interpret y
    Mul x y -> zipWith (*) <$> interpret x <*> interpret y
    Div x y -> zipWith (/) <$> interpret x <*> interpret y
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
    IfNum p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
    IfBool p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
    ToBool x -> interpret x
    ToNum x -> interpret x

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = ReaderT Heap (StateT (Witness n) (Except (InterpretError n)))

runM :: Heap -> Witness n -> M n a -> Either (InterpretError n) (a, Witness n)
runM heap bindings p = runExcept (runStateT (runReaderT p heap) bindings)

runMWithInputs :: Elaborated t -> [n] -> M n a -> Either (InterpretError n) (a, Witness n)
runMWithInputs elab inputs = runM heap bindings
  where
    comp = elabComp elab
    bindings = IntMap.fromAscList $ zip (IntSet.toAscList (compInputVars comp)) inputs
    heap = compHeap comp

lookupVar :: Show n => Int -> M n n
lookupVar var = do
  bindings <- get
  case IntMap.lookup var bindings of
    Nothing -> throwError $ InterpretUnboundVarError var bindings
    Just val -> return val

lookupAddr :: Show n => Int -> M n [n]
lookupAddr addr = do
  heap <- ask
  case IntMap.lookup addr heap of
    Nothing -> throwError $ InterpretUnboundAddrError addr heap
    Just (elemType, array) -> case elemType of
      NumElem -> mapM lookupVar (IntMap.elems array)
      BoolElem -> mapM lookupVar (IntMap.elems array)
      (ArrElem _ _) -> concat <$> mapM lookupAddr (IntMap.elems array)

addBinding :: Ref t -> [n] -> M n ()
addBinding _ [] = error "addBinding: empty list"
addBinding (BoolVar var) [val] = modify (IntMap.insert var val)
addBinding (NumVar var) [val] = modify (IntMap.insert var val)
addBinding (ArrayRef _ _ addr) vals = do
  vars <- collectVarsFromAddr addr
  mapM_
    (modify . uncurry IntMap.insert)
    (zip vars vals)
  where
    collectVarsFromAddr :: Addr -> M n [Var]
    collectVarsFromAddr address = do
      heap <- ask
      case IntMap.lookup address heap of
        Nothing -> throwError $ InterpretUnboundAddrError addr heap
        Just (elemType, array) -> case elemType of
          NumElem -> return $ IntMap.elems array
          BoolElem -> return $ IntMap.elems array
          (ArrElem _ _) -> concat <$> mapM collectVarsFromAddr (IntMap.elems array)
addBinding _ _ = error "addBinding: too many values"

--------------------------------------------------------------------------------

data InterpretError n
  = InterpretUnboundVarError Var (Witness n)
  | InterpretUnboundAddrError Addr Heap
  | InterpretAssertionError (Val 'Bool) (Witness n)
  | InterpretVarUnassignedError IntSet (Witness n)
  | InterpretInputSizeError Int Int
  deriving (Eq)

instance (GaloisField n, Integral n) => Show (InterpretError n) where
  show (InterpretUnboundVarError var bindings) =
    "unbound variable " ++ show var
      ++ " in bindings "
      ++ showWitness bindings
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
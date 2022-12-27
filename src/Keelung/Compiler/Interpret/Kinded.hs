{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}

module Keelung.Compiler.Interpret.Kinded
  ( run,
    runAndCheck,
    FreeVar,
    Interpret,
    bitWiseRotateL,
    bitWiseShiftL,
  )
where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bits (Bits (..))
import Data.Foldable (toList)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Semiring (Semiring (..))
import qualified Data.Sequence as Seq
import GHC.TypeLits (KnownNat)
import Keelung hiding (inputs, interpret, run)
import Keelung.Compiler.Syntax.Inputs (Inputs)
import qualified Keelung.Compiler.Syntax.Inputs as Inputs
import Keelung.Compiler.Util
import Keelung.Syntax.Counters
import Keelung.Types

--------------------------------------------------------------------------------

-- | Interpret a program with inputs.
run' :: (FreeVar t, Interpret t n, GaloisField n, Integral n) => Elaborated t -> Inputs n -> Either (InterpretError n) ([n], Witness n)
run' elab inputs = runM elab inputs $ do
  let (Elaborated expr comp) = elab
  -- interpret the assignments first
  -- reverse the list assignments so that "simple values" are binded first
  -- see issue#3: https://github.com/btq-ag/keelung-compiler/issues/3

  -- interpret assignments of values first
  assignmentsF <-
    filterM
      ( \(var, e) -> case e of
          Integer val -> interpret val >>= addBinding var >> return False
          Rational val -> interpret val >>= addBinding var >> return False
          _ -> return True
      )
      (IntMap.toList (compAssignmentF comp))
  assignmentsB <-
    filterM
      ( \(var, e) -> case e of
          Boolean val -> interpret val >>= addBinding var >> return False
          _ -> return True
      )
      (IntMap.toList (compAssignmentB comp))
  -- interpret the rest of the assignments
  forM_ assignmentsF $ \(var, e) -> interpret e >>= addBinding var
  forM_ assignmentsB $ \(var, e) -> interpret e >>= addBinding var

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
run :: (FreeVar t, Interpret t n, GaloisField n, Integral n) => Elaborated t -> Inputs n -> Either (InterpretError n) [n]
run elab inputs = fst <$> run' elab inputs

-- | Interpret a program with inputs and run some additional checks.
runAndCheck :: (FreeVar t, Interpret t n, GaloisField n, Integral n) => Elaborated t -> Inputs n -> Either (InterpretError n) [n]
runAndCheck elab inputs = do
  (output, witness) <- run' elab inputs

  -- See if input size is valid
  let (Elaborated _ comp) = elab
  let expectedInputSize = getCountBySort OfInput (compCounters comp)
  let actualInputSize = Inputs.size inputs
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

instance FreeVar Field where
  freeVars expr = case expr of
    Integer _ -> return mempty
    Rational _ -> return mempty
    VarF var -> return $ IntSet.singleton var
    VarFI _ -> return mempty
    Add x y -> (<>) <$> freeVars x <*> freeVars y
    Sub x y -> (<>) <$> freeVars x <*> freeVars y
    Mul x y -> (<>) <$> freeVars x <*> freeVars y
    Div x y -> (<>) <$> freeVars x <*> freeVars y
    IfF x y z -> (<>) <$> freeVars x <*> ((<>) <$> freeVars y <*> freeVars z)
    BtoF x -> freeVars x

instance FreeVar Boolean where
  freeVars expr = case expr of
    Boolean _ -> return mempty
    VarB var -> return $ IntSet.singleton var
    VarBI _ -> return mempty
    And x y -> (<>) <$> freeVars x <*> freeVars y
    Or x y -> (<>) <$> freeVars x <*> freeVars y
    Xor x y -> (<>) <$> freeVars x <*> freeVars y
    Not x -> freeVars x
    EqB x y -> (<>) <$> freeVars x <*> freeVars y
    EqF x y -> (<>) <$> freeVars x <*> freeVars y
    EqU x y -> (<>) <$> freeVars x <*> freeVars y
    IfB x y z -> (<>) <$> freeVars x <*> ((<>) <$> freeVars y <*> freeVars z)
    BitU x _ -> freeVars x

instance FreeVar (UInt w) where
  freeVars val = case val of
    UInt _ -> return mempty
    VarU var -> return $ IntSet.singleton var
    VarUI _ -> return mempty
    AddU x y -> (<>) <$> freeVars x <*> freeVars y
    SubU x y -> (<>) <$> freeVars x <*> freeVars y
    MulU x y -> (<>) <$> freeVars x <*> freeVars y
    AndU x y -> (<>) <$> freeVars x <*> freeVars y
    OrU x y -> (<>) <$> freeVars x <*> freeVars y
    XorU x y -> (<>) <$> freeVars x <*> freeVars y
    NotU x -> freeVars x
    RoLU _ _ x -> freeVars x
    ShLU _ _ x -> freeVars x
    IfU p x y -> (<>) <$> freeVars p <*> ((<>) <$> freeVars x <*> freeVars y)
    BtoU x -> freeVars x

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
            ElemF -> return $ IntSet.fromList (IntMap.elems array)
            ElemB -> return $ IntSet.fromList (IntMap.elems array)
            (ElemArr _ _) -> IntSet.unions <$> mapM freeVarsOfArray (IntMap.elems array)
            ElemU _ -> return $ IntSet.fromList (IntMap.elems array)

-- | Collect free variables of an elaborated program (excluding input variables).
instance FreeVar t => FreeVar (Elaborated t) where
  freeVars (Elaborated value comp) = do
    inOutputValue <- freeVars value
    inNumBindings <- forM (IntMap.toList (compAssignmentF comp)) $ \(var, val) -> do
      -- collect both the var and its value
      IntSet.insert var <$> freeVars val
    inBoolBindings <- forM (IntMap.toList (compAssignmentB comp)) $ \(var, val) -> do
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

instance (GaloisField n, Integral n) => Interpret Field n where
  interpret val = case val of
    Integer n -> interpret n
    Rational n -> interpret n
    VarF var -> pure <$> lookupVar var
    VarFI var -> pure <$> lookupVarFI var
    Add x y -> zipWith (+) <$> interpret x <*> interpret y
    Sub x y -> zipWith (-) <$> interpret x <*> interpret y
    Mul x y -> zipWith (*) <$> interpret x <*> interpret y
    Div x y -> zipWith (/) <$> interpret x <*> interpret y
    IfF p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
    BtoF x -> interpret x

instance (GaloisField n, Integral n) => Interpret Boolean n where
  interpret val = case val of
    Boolean b -> interpret b
    VarB var -> pure <$> lookupVar var
    VarBI var -> pure <$> lookupVarBI var
    And x y -> zipWith (*) <$> interpret x <*> interpret y
    Or x y -> zipWith (+) <$> interpret x <*> interpret y
    Xor x y -> zipWith (\x' y' -> x' + y' - 2 * (x' * y')) <$> interpret x <*> interpret y
    Not x -> map (1 -) <$> interpret x
    IfB p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
    EqB x y -> do
      x' <- interpret x
      y' <- interpret y
      interpret (x' == y')
    EqF x y -> do
      x' <- interpret x
      y' <- interpret y
      interpret (x' == y')
    EqU x y -> do
      x' <- interpret x
      y' <- interpret y
      interpret (x' == y')
    BitU x i -> do
      xs <- interpret x
      if testBit (toInteger (head xs)) i
        then return [one]
        else return [zero]

instance (GaloisField n, Integral n, KnownNat w) => Interpret (UInt w) n where
  interpret val = case val of
    UInt n -> interpret n
    VarU var -> pure <$> lookupVar var
    VarUI var -> pure <$> lookupVarUI (widthOf val) var
    AddU x y -> zipWith (+) <$> interpret x <*> interpret y
    SubU x y -> zipWith (-) <$> interpret x <*> interpret y
    MulU x y -> zipWith (*) <$> interpret x <*> interpret y
    -- UIntDiv x y -> zipWith (/) <$> interpret x <*> interpret y
    AndU x y -> zipWith bitWiseAnd <$> interpret x <*> interpret y
    OrU x y -> zipWith bitWiseOr <$> interpret x <*> interpret y
    XorU x y -> zipWith bitWiseXor <$> interpret x <*> interpret y
    NotU x -> map bitWiseNot <$> interpret x
    RoLU w n x -> map (bitWiseRotateL w n) <$> interpret x
    ShLU w n x -> map (bitWiseShiftL w n) <$> interpret x
    IfU p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
    BtoU x -> interpret x

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
type M n = ReaderT (Inputs n, Heap) (StateT (Witness n) (Except (InterpretError n)))

runM :: Show n => Elaborated t -> Inputs n -> M n a -> Either (InterpretError n) (a, Witness n)
runM elab inputs p =
  runExcept (runStateT (runReaderT p (inputs, heap)) mempty)
  where
    (Elaborated _ comp) = elab
    heap = compHeap comp

lookupVar :: Show n => Int -> M n n
lookupVar var = do
  bindings <- get
  case IntMap.lookup var bindings of
    Nothing -> throwError $ InterpretUnboundVarError var bindings
    Just val -> return val

lookupVarFI :: Show n => Var -> M n n
lookupVarFI var = do
  inputs <- asks (Inputs.numInputs . fst)
  case inputs Seq.!? var of
    Nothing -> throwError $ InterpretUnboundInputVarError var (IntMap.fromDistinctAscList (zip [0 ..] (toList inputs)))
    Just val -> return val

lookupVarBI :: Show n => Var -> M n n
lookupVarBI var = do
  inputs <- asks (Inputs.boolInputs . fst)
  case inputs Seq.!? var of
    Nothing -> throwError $ InterpretUnboundInputVarError var (IntMap.fromDistinctAscList (zip [0 ..] (toList inputs)))
    Just val -> return val

lookupVarUI :: Show n => Int -> Var -> M n n
lookupVarUI width var = do
  inputss <- asks (Inputs.uintInputs . fst)
  case IntMap.lookup width inputss of
    Nothing -> error ("lookupVarUI: no UInt of such bit width: " <> show width)
    Just inputs ->
      case inputs Seq.!? var of
        Nothing -> throwError $ InterpretUnboundInputVarError var (IntMap.fromDistinctAscList (zip [0 ..] (toList inputs)))
        Just val -> return val

lookupAddr :: Show n => Int -> M n [n]
lookupAddr addr = do
  heap <- asks snd
  case IntMap.lookup addr heap of
    Nothing -> throwError $ InterpretUnboundAddrError addr heap
    Just (elemType, array) -> case elemType of
      ElemF -> mapM lookupVar (IntMap.elems array)
      ElemB -> mapM lookupVar (IntMap.elems array)
      (ElemArr _ _) -> concat <$> mapM lookupAddr (IntMap.elems array)
      ElemU _ -> mapM lookupVar (IntMap.elems array)

addBinding :: Var -> [n] -> M n ()
addBinding var [val] = modify (IntMap.insert var val)
addBinding _ _ = error "addBinding: expected a single value"

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
    "unbound variable $" ++ show var
      ++ " in bindings "
      ++ showWitness bindings
  show (InterpretUnboundInputVarError var inputs) =
    "unbound input variable $" ++ show var
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

--------------------------------------------------------------------------------

bitWiseAnd :: (GaloisField n, Integral n) => n -> n -> n
bitWiseAnd x y = fromInteger $ (Data.Bits..&.) (toInteger x) (toInteger y)

bitWiseOr :: (GaloisField n, Integral n) => n -> n -> n
bitWiseOr x y = fromInteger $ (Data.Bits..|.) (toInteger x) (toInteger y)

bitWiseXor :: (GaloisField n, Integral n) => n -> n -> n
bitWiseXor x y = fromInteger $ Data.Bits.xor (toInteger x) (toInteger y)

bitWiseNot :: (GaloisField n, Integral n) => n -> n
bitWiseNot x = fromInteger $ Data.Bits.complement (toInteger x)

-- w is the bit width of the result
-- n is the amount to shift left by
-- x is the value to shift
bitWiseRotateL :: (GaloisField n, Integral n) => Width -> Int -> n -> n
bitWiseRotateL w n x =
  fromInteger $
    (toInteger x `Data.Bits.shiftL` fromIntegral (n `mod` w) Data.Bits..&. (2 ^ w - 1))
      Data.Bits..|. (toInteger x `Data.Bits.shiftR` fromIntegral (w - (n `mod` w)))

bitWiseShiftL :: (GaloisField n, Integral n) => Width -> Int -> n -> n
bitWiseShiftL w n x =
  if n < 0
    then fromInteger $ Data.Bits.shiftR (toInteger x) (-n)
    else fromInteger $ Data.Bits.shiftL (toInteger x) n Data.Bits..&. (2 ^ w - 1)
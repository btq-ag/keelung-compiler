{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- Interpreter for Keelung.Syntax.Typed
{-# LANGUAGE TupleSections #-}

module Keelung.Compiler.Interpret.Typed (InterpretError (..), runAndOutputWitnesses, run, runAndCheck) where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bits (Bits (..))
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Semiring (Semiring (..))
import qualified Data.Sequence as Seq
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung (N (N))
import Keelung.Compiler.Syntax.Inputs (Inputs)
import qualified Keelung.Compiler.Syntax.Inputs as Inputs
import Keelung.Compiler.Util
import Keelung.Syntax.Typed
import Keelung.Syntax.VarCounters
import Keelung.Types

--------------------------------------------------------------------------------

-- | Interpret a program with inputs and return outputs along with the witness
runAndOutputWitnesses :: (GaloisField n, Integral n) => Elaborated -> Inputs n -> Either (InterpretError n) ([n], Witness n)
runAndOutputWitnesses (Elaborated expr comp) inputs = runM inputs $ do
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
      let (freeNumInputVars, freeBoolInputVars, freeCustomInputVars, freeIntermediateVars) = freeVars e
      numInputBindings <- mapM (\var -> ("$N" <> show var,) <$> lookupNumInputVar var) $ IntSet.toList freeNumInputVars
      boolInputBindings <- mapM (\var -> ("$B" <> show var,) <$> lookupBoolInputVar var) $ IntSet.toList freeBoolInputVars
      -- let customInputBindings = 
      --       map 
      --         (\(width, vars) -> map (\var -> ("$U" <> show var,) <$> lookupUIntInputVar width var) (IntSet.toList vars))
      --         (IntMap.toList freeCustomInputVars)
      intermediateBindings <- mapM (\var -> ("$" <> show var,) <$> lookupVar var) $ IntSet.toList freeIntermediateVars
      -- collect variables and their bindings in the expression and report them
      throwError $ InterpretAssertionError e (numInputBindings <> boolInputBindings <> intermediateBindings)

  -- lastly interpret the expression and return the result
  interpret expr

-- | Interpret a program with inputs.
run :: (GaloisField n, Integral n) => Elaborated -> Inputs n -> Either (InterpretError n) [n]
run elab inputs = fst <$> runAndOutputWitnesses elab inputs

-- | Interpret a program with inputs and run some additional checks.
runAndCheck :: (GaloisField n, Integral n) => Elaborated -> Inputs n -> Either (InterpretError n) [n]
runAndCheck elab inputs = do
  (output, witness) <- runAndOutputWitnesses elab inputs

  -- See if input size is valid
  let expectedInputSize = inputVarSize (compVarCounters (elabComp elab))
  let actualInputSize = length (Inputs.numInputs inputs <> Inputs.boolInputs inputs)
  when (expectedInputSize /= actualInputSize) $ do
    throwError $ InterpretInputSizeError expectedInputSize actualInputSize

  -- See if free variables of the program and the witness are the same
  let variables = freeIntermediateVarsOfElab elab
  let varsInWitness = IntMap.keysSet witness
  when (variables /= varsInWitness) $ do
    let missingInWitness = variables IntSet.\\ varsInWitness
    let missingInProgram = IntMap.withoutKeys witness variables
    throwError $ InterpretVarUnassignedError missingInWitness missingInProgram

  return output

--------------------------------------------------------------------------------

-- | The interpreter typeclass
class Interpret a n where
  interpret :: a -> M n [n]

instance GaloisField n => Interpret Bool n where
  interpret True = return [one]
  interpret False = return [zero]

instance GaloisField n => Interpret Val n where
  interpret (Integer n) = return [fromIntegral n]
  interpret (Rational n) = return [fromRational n]
  interpret (Unsigned _ n) = return [fromIntegral n]
  interpret (Boolean b) = interpret b
  interpret Unit = return []

instance (GaloisField n, Integral n) => Interpret Expr n where
  interpret expr = case expr of
    Val val -> interpret val
    Var (NumVar n) -> pure <$> lookupVar n
    Var (NumInputVar n) -> pure <$> lookupNumInputVar n
    Var (BoolVar n) -> pure <$> lookupVar n
    Var (BoolInputVar n) -> pure <$> lookupBoolInputVar n
    Var (UIntVar _ n) -> pure <$> lookupVar n
    Var (UIntInputVar width n) -> pure <$> lookupUIntInputVar width n
    Array xs -> concat <$> mapM interpret xs
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
    If b x y -> do
      b' <- interpret b
      case b' of
        [0] -> interpret y
        _ -> interpret x
    ToNum x -> interpret x
    Bit x i -> do
      xs <- interpret x
      if testBit (toInteger (head xs)) i
        then return [one]
        else return [zero]

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = ReaderT (Inputs n) (StateT (IntMap n) (Except (InterpretError n)))

runM :: Inputs n -> M n a -> Either (InterpretError n) (a, Witness n)
runM inputs p = runExcept (runStateT (runReaderT p inputs) mempty)

-- | A `Ref` is given a list of numbers
-- but in reality it should be just a single number.
addBinding :: Ref -> [n] -> M n ()
addBinding _ [] = error "addBinding: empty list"
addBinding (NumVar var) val = modify (IntMap.insert var (head val))
addBinding (BoolVar var) val = modify (IntMap.insert var (head val))
addBinding _ _ = error "addBinding: not NumVar or BoolVar"

lookupVar :: Show n => Var -> M n n
lookupVar var = do
  bindings <- get
  case IntMap.lookup var bindings of
    Nothing -> throwError $ InterpretUnboundVarError var bindings
    Just val -> return val

lookupNumInputVar :: Show n => Var -> M n n
lookupNumInputVar var = do
  inputs <- asks Inputs.numInputs
  case inputs Seq.!? var of
    Nothing -> throwError $ InterpretUnboundVarError var (IntMap.fromDistinctAscList (zip [0 ..] (toList inputs)))
    Just val -> return val

lookupBoolInputVar :: Show n => Var -> M n n
lookupBoolInputVar var = do
  inputs <- asks Inputs.boolInputs
  case inputs Seq.!? var of
    Nothing -> throwError $ InterpretUnboundVarError var (IntMap.fromDistinctAscList (zip [0 ..] (toList inputs)))
    Just val -> return val

lookupUIntInputVar :: Show n => Int -> Var -> M n n
lookupUIntInputVar width var = do
  inputss <- asks Inputs.uintInputs
  case IntMap.lookup width inputss of
    Nothing -> error ("lookupUIntInputVar: no UInt of such bit width: " <> show width)
    Just inputs ->
      case inputs Seq.!? var of
        Nothing -> throwError $ InterpretUnboundVarError var (IntMap.fromDistinctAscList (zip [0 ..] (toList inputs)))
        Just val -> return val

--------------------------------------------------------------------------------

-- | Collect free variables of an elaborated program (that should also be present in the witness)
freeIntermediateVarsOfElab :: Elaborated -> IntSet
freeIntermediateVarsOfElab (Elaborated value context) =
  let (_, _, _, inOutputValue) = freeVars value
      inNumBindings =
        map
          (\(Assignment (NumVar var) val) -> let (_, _, _, vars) = freeVars val in IntSet.insert var vars) -- collect both the var and its value
          (compNumAsgns context)
      inBoolBindings =
        map
          (\(Assignment (BoolVar var) val) -> let (_, _, _, vars) = freeVars val in IntSet.insert var vars) -- collect both the var and its value
          (compBoolAsgns context)
   in inOutputValue
        <> IntSet.unions inNumBindings
        <> IntSet.unions inBoolBindings

-- | Collect variables of an expression and group them into sets of:
--    1. Number input variables
--    2. Boolean input variables
--    3. Custom input variables
--    4. intermediate variables
freeVars :: Expr -> (IntSet, IntSet, IntMap IntSet, IntSet)
freeVars expr = case expr of
  Val _ -> mempty
  Var (NumVar n) -> (mempty, mempty, mempty, IntSet.singleton n)
  Var (NumInputVar n) -> (IntSet.singleton n, mempty, mempty, mempty)
  Var (BoolVar n) -> (mempty, mempty, mempty, IntSet.singleton n)
  Var (BoolInputVar n) -> (mempty, IntSet.singleton n, mempty, mempty)
  Var (UIntVar _ n) -> (mempty, mempty, mempty, IntSet.singleton n)
  Var (UIntInputVar w n) -> (mempty, mempty, IntMap.singleton w (IntSet.singleton n), mempty)
  Array xs ->
    let unzip4 = foldr (\(u, y, z, w) (us, ys, zs, ws) -> (u : us, y : ys, z : zs, w : ws)) mempty
        (ns, bs, cs, os) = unzip4 $ toList $ fmap freeVars xs
     in (IntSet.unions ns, IntSet.unions bs, IntMap.unionsWith (<>) cs, IntSet.unions os)
  Add x y -> freeVars x <> freeVars y
  Sub x y -> freeVars x <> freeVars y
  Mul x y -> freeVars x <> freeVars y
  Div x y -> freeVars x <> freeVars y
  Eq x y -> freeVars x <> freeVars y
  And x y -> freeVars x <> freeVars y
  Or x y -> freeVars x <> freeVars y
  Xor x y -> freeVars x <> freeVars y
  BEq x y -> freeVars x <> freeVars y
  If x y z -> freeVars x <> freeVars y <> freeVars z
  ToNum x -> freeVars x
  Bit x _ -> freeVars x

--------------------------------------------------------------------------------

data InterpretError n
  = InterpretUnboundVarError Var (Witness n)
  | InterpretUnboundAddrError Addr Heap
  | InterpretAssertionError Expr [(String, n)]
  | InterpretVarUnassignedError IntSet (Witness n)
  | InterpretInputSizeError Int Int
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (InterpretError n)

instance (GaloisField n, Integral n) => Show (InterpretError n) where
  show (InterpretUnboundVarError var witness) =
    "unbound variable $" ++ show var
      ++ " in witness "
      ++ showWitness witness
  show (InterpretUnboundAddrError var heap) =
    "unbound address " ++ show var
      ++ " in heap "
      ++ show heap
  show (InterpretAssertionError expr assignments) =
    "assertion failed: " <> show expr
      <> "\nassignment of variables:\n"
      <> unlines (map (\(var, val) -> "  " <> var <> " := " <> show (N val)) assignments)
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
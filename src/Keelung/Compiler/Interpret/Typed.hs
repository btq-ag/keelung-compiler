{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- Interpreter for Keelung.Syntax.Typed
{-# LANGUAGE TupleSections #-}

module Keelung.Compiler.Interpret.Typed (InterpretError (..), run, runAndCheck) where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Semiring (Semiring (..))
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung.Compiler.Util
import Keelung.Syntax.Typed
import Keelung.Types (Addr, Heap, Var)
import Control.Monad.Reader

--------------------------------------------------------------------------------

-- | Interpret a program with inputs and return outputs along with the witness
run' :: GaloisField n => Elaborated -> [n] -> Either (InterpretError n) ([n], Witness n)
run' (Elaborated expr comp) inputs = runM inputs $ do
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
      let vars = freeVars e
      bindings' <- mapM (\var -> (var,) <$> lookupVar var) $ IntSet.toList vars
      throwError $ InterpretAssertionError e (IntMap.fromList bindings')

  -- lastly interpret the expression and return the result
  interpret expr

-- | Interpret a program with inputs.
run :: GaloisField n => Elaborated -> [n] -> Either (InterpretError n) [n]
run (Elaborated expr comp) inputs = fst <$> run' (Elaborated expr comp) inputs

-- | Interpret a program with inputs and run some additional checks.
runAndCheck :: GaloisField n => Elaborated -> [n] -> Either (InterpretError n) [n]
runAndCheck elab inputs = do
  (output, witness) <- run' elab inputs

  -- See if input size is valid
  let expectedInputSize = compNextInputVar (elabComp elab) - 1
  let actualInputSize = length inputs
  when (expectedInputSize /= actualInputSize) $ do
    throwError $ InterpretInputSizeError expectedInputSize actualInputSize

  -- See if free variables of the program and the witness are the same
  let variables = freeVarsOfElab elab
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
  interpret (Boolean b) = interpret b
  interpret Unit = return []

instance GaloisField n => Interpret Expr n where
  interpret expr = case expr of
    Val val -> interpret val
    Var (NumVar n) -> pure <$> lookupVar n
    Var (NumInputVar n) -> pure <$> lookupInputVar n
    Var (BoolVar n) -> pure <$> lookupVar n
    Var (BoolInputVar n) -> pure <$> lookupInputVar n
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
    ToBool x -> interpret x
    ToNum x -> interpret x

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = ReaderT (IntMap n) (StateT (IntMap n) (Except (InterpretError n)))

runM :: [n] -> M n a -> Either (InterpretError n) (a, Witness n)
runM inputs p = runExcept (runStateT (runReaderT p inputBindings) mempty)
  where 
    inputBindings = IntMap.fromDistinctAscList $ zip [0..] inputs

-- | A `Ref` is given a list of numbers
-- but in reality it should be just a single number.
addBinding :: Ref -> [n] -> M n ()
addBinding _ [] = error "addBinding: empty list"
addBinding (NumVar var) val = modify (IntMap.insert var (head val))
addBinding (BoolVar var) val = modify (IntMap.insert var (head val))
addBinding _ _ = error "addBinding: not NumVar or BoolVar"

lookupVar :: Show n => Int -> M n n
lookupVar var = do
  bindings <- get
  case IntMap.lookup var bindings of
    Nothing -> throwError $ InterpretUnboundVarError var bindings
    Just val -> return val

lookupInputVar :: Show n => Int -> M n n
lookupInputVar var = do
  bindings <- ask
  case IntMap.lookup var bindings of
    Nothing -> throwError $ InterpretUnboundVarError var bindings
    Just val -> return val

--------------------------------------------------------------------------------

-- | Collect free variables of an elaborated program (that should also be present in the witness)
freeVarsOfElab :: Elaborated -> IntSet
freeVarsOfElab (Elaborated value context) =
  let inOutputValue = freeVars value
      inputBindings = IntSet.fromDistinctAscList [0 .. compNextInputVar context - 1]
      inNumBindings =
        map
          (\(Assignment (NumVar var) val) -> IntSet.insert var (freeVars val)) -- collect both the var and its value
          (compNumAsgns context)
      inBoolBindings =
        map
          (\(Assignment (BoolVar var) val) -> IntSet.insert var (freeVars val)) -- collect both the var and its value
          (compBoolAsgns context)
   in inputBindings
        <> inOutputValue
        <> IntSet.unions inNumBindings
        <> IntSet.unions inBoolBindings

--------------------------------------------------------------------------------

data InterpretError n
  = InterpretUnboundVarError Var (Witness n)
  | InterpretUnboundAddrError Addr Heap
  | InterpretAssertionError Expr (Witness n)
  | InterpretVarUnassignedError IntSet (Witness n)
  | InterpretInputSizeError Int Int
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (InterpretError n)

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
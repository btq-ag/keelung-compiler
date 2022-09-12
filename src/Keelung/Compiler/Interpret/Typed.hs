-- Interpreter for Keelung.Syntax.Typed
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Keelung.Compiler.Interpret.Typed (run) where 

import Control.Monad.Except
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Semiring (Semiring (..))
import Keelung.Field (N (..))
import Keelung.Syntax.Typed

--------------------------------------------------------------------------------

run :: GaloisField n => Elaborated -> [n] -> Either (InterpretError n) [n]
run (Elaborated expr comp) inputs = runM bindings $ do
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
  where
    bindings = IntMap.fromAscList $ zip (IntSet.toAscList (compInputVars comp)) inputs

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
    Var (BoolVar n) -> pure <$> lookupVar n
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
type M n = StateT (IntMap n) (Except (InterpretError n))

runM :: IntMap n -> M n a -> Either (InterpretError n) a
runM st p = runExcept (evalStateT p st)

-- | A `Ref` is given a list of numbers
-- but in reality it should be just a single number.
addBinding :: Ref -> [n] -> M n ()
addBinding _ [] = error "addBinding: empty list"
addBinding (NumVar var) val = modify (IntMap.insert var (head val))
addBinding (BoolVar var) val = modify (IntMap.insert var (head val))

lookupVar :: Show n => Int -> M n n
lookupVar var = do
  bindings <- get
  case IntMap.lookup var bindings of
    Nothing -> throwError $ InterpretUnboundVarError var bindings
    Just val -> return val

--------------------------------------------------------------------------------

data InterpretError n
  = InterpretUnboundVarError Int (IntMap n)
  | InterpretAssertionError Expr (IntMap n)
  deriving (Eq)

instance (GaloisField n, Integral n) => Show (InterpretError n) where
  show (InterpretUnboundVarError var bindings) =
    "unbound variable " ++ show var
      ++ " in bindings "
      ++ show (fmap N bindings)
  show (InterpretAssertionError expr bindings) =
    "assertion failed: " ++ show expr
      ++ "\nbindings of variables: "
      ++ show (fmap N bindings)

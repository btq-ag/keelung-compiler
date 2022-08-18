{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}

module Keelung.Compiler.Interpret (InterpretError (..), run) where

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

-- | The interpreter typeclass
class Interpret a n where
  interp :: a -> M n [n]

instance GaloisField n => Interpret Bool n where
  interp True = return [one]
  interp False = return [zero]

instance GaloisField n => Interpret Val n where
  interp (Number n) = return [fromIntegral n]
  interp (Boolean b) = interp b
  interp Unit = return []

instance GaloisField n => Interpret Expr n where
  interp expr = case expr of
    Val val -> interp val
    Var (NumVar n) -> pure <$> lookupVar n
    Var (BoolVar n) -> pure <$> lookupVar n
    Array xs -> concat <$> mapM interp xs 
    Add x y -> zipWith (+) <$> interp x <*> interp y
    Sub x y -> zipWith (-) <$> interp x <*> interp y
    Mul x y -> zipWith (*) <$> interp x <*> interp y
    Div x y -> zipWith (/) <$> interp x <*> interp y
    Eq x y -> do
      x' <- interp x
      y' <- interp y
      interp (x' == y')
    And x y -> zipWith (*) <$> interp x <*> interp y
    Or x y -> zipWith (+) <$> interp x <*> interp y
    Xor x y -> zipWith (\x' y' -> x' + y' - 2 * (x' * y')) <$> interp x <*> interp y
    BEq x y -> do
      x' <- interp x
      y' <- interp y
      interp (x' == y')
    If b x y -> do
      b' <- interp b
      case b' of
        [0] -> interp y
        _ -> interp x
    ToBool x -> interp x
    ToNum x -> interp x

--------------------------------------------------------------------------------

run :: (GaloisField n, Bounded n, Integral n) => Elaborated -> [n] -> Either (InterpretError n) [n]
run (Elaborated expr comp) inputs = runM bindings $ do
  -- interpret the assignments first
  -- reverse the list assignments so that "simple values" are binded first
  -- see issue#3: https://github.com/btq-ag/keelung-compiler/issues/3
  let numAssignments = reverse (compNumAsgns comp)
  forM_ numAssignments $ \(Assignment var e) -> do
    values <- interp e
    addBinding var values

  let boolAssignments = reverse (compBoolAsgns comp)
  forM_ boolAssignments $ \(Assignment var e) -> do
    values <- interp e
    addBinding var values

  -- interpret the assertions next
  -- throw error if any assertion fails
  forM_ (compAssertions comp) $ \e -> do
    values <- interp e
    when (values /= [1]) $ do
      -- collect variables and their bindings in the expression
      let vars = freeVars e
      bindings' <- mapM (\var -> (var,) <$> lookupVar var) $ IntSet.toList vars
      throwError $ InterpretAssertionError e (IntMap.fromList bindings')

  -- lastly interpret the expression and return the result
  interp expr
  where
    bindings = IntMap.fromAscList $ zip (IntSet.toAscList (compInputVars comp)) inputs

--------------------------------------------------------------------------------

data InterpretError n
  = InterpretUnboundVarError Int (IntMap n)
  | InterpretAssertionError Expr (IntMap n)
  deriving (Eq)

instance (Show n, Bounded n, Integral n, Fractional n) => Show (InterpretError n) where
  show (InterpretUnboundVarError var bindings) =
    "unbound variable " ++ show var
      ++ " in bindings "
      ++ show (fmap N bindings)
  show (InterpretAssertionError expr bindings) =
    "assertion failed: " ++ show expr
      ++ "\nbindings of variables: "
      ++ show (fmap N bindings)

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}

module Keelung.Interpret (InterpretError (..), interpretElaborated) where

import Control.Monad.Except
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Semiring (Semiring (..))
import Keelung.Monad (Assignment (..), Computation (..), Elaborated (..))
import Keelung.Syntax
import Keelung.Syntax.Common (Var)
import Keelung.Util (DebugGF (..))

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = StateT (IntMap n) (Except (InterpretError n))

runM :: IntMap n -> M n a -> Either (InterpretError n) a
runM st p = runExcept (evalStateT p st)

addBinding :: Int -> n -> M n ()
addBinding var val = modify $ \xs -> IntMap.insert var val xs

lookupVar :: Show n => Int -> M n n
lookupVar var = do
  bindings <- get
  case IntMap.lookup var bindings of
    Nothing -> throwError $ InterpretUnboundVarError var bindings
    Just val -> return val

--------------------------------------------------------------------------------

-- | The interpreter typeclass
class Interpret a n where
  interp :: a -> M n n

instance GaloisField n => Interpret Bool n where
  interp True = return one
  interp False = return zero

instance GaloisField n => Interpret (Value ty n) n where
  interp v = case v of
    Number n -> return n
    Boolean b -> interp b

instance GaloisField n => Interpret (Expr ty n) n where
  interp expr = case expr of
    Val val -> interp val
    Var (Variable n) -> lookupVar n
    Add x y -> (+) <$> interp x <*> interp y
    Sub x y -> (-) <$> interp x <*> interp y
    Mul x y -> (*) <$> interp x <*> interp y
    Div x y -> (/) <$> interp x <*> interp y
    Eq x y -> do
      x' <- interp x
      y' <- interp y
      interp (x' == y')
    And x y -> (*) <$> interp x <*> interp y
    Or x y -> (+) <$> interp x <*> interp y
    Xor x y -> do
      x' <- interp x
      y' <- interp y
      return $ x' + y' - x' * y'
    BEq x y -> do
      x' <- interp x
      y' <- interp y
      interp (x' == y')
    IfThenElse b x y -> do
      b' <- interp b
      case b' of
        0 -> interp y
        _ -> interp x
    ToBool x -> interp x
    ToNum x -> interp x

--------------------------------------------------------------------------------

interpretElaborated :: (GaloisField n, Bounded n, Integral n) => Elaborated ty n -> [n] -> Either (InterpretError n) (Maybe n)
interpretElaborated (Elaborated expr comp) inputs = runM bindings $ do
  -- interpret the assignments first
  forM_ (compNumAsgns comp) $ \(Assignment (Variable var) e) -> do
    value <- interp e
    addBinding var value

  forM_ (compBoolAsgns comp) $ \(Assignment (Variable var) e) -> do
    value <- interp e
    addBinding var value

  -- interpret the assertions next
  -- throw error if any assertion fails
  forM_ (compAssertions comp) $ \e -> do
    value <- interp e
    when (value /= 1) $ do
      -- collect variables and their bindings in the expression
      let vars = freeVars e
      bindings' <- mapM (\var -> (var,) <$> lookupVar var) $ IntSet.toList vars
      throwError $ InterpretAssertionError e (IntMap.fromList bindings')

  -- lastly interpret the expression and return the result
  mapM interp expr
  where
    bindings = IntMap.fromAscList $ zip (IntSet.toAscList (compInputVars comp)) inputs

--------------------------------------------------------------------------------

data InterpretError n
  = InterpretUnboundVarError Var (IntMap n)
  | InterpretAssertionError (Expr 'Bool n) (IntMap n)
  deriving (Eq)

instance (Show n, Bounded n, Integral n, Fractional n) => Show (InterpretError n) where
  show (InterpretUnboundVarError var bindings) =
    "unbound variable " ++ show var
      ++ " in bindings "
      ++ show (fmap DebugGF bindings)
  show (InterpretAssertionError expr bindings) =
    "assertion failed: " ++ show (fmap DebugGF expr)
      ++ "\nbindings of variables: "
      ++ show (fmap DebugGF bindings)

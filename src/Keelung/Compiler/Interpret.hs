{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}

module Keelung.Compiler.Interpret (InterpretError (..), interpretElaborated2) where

import Control.Monad.Except
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Semiring (Semiring (..))
import Keelung.Field (N (..))
import Keelung.Syntax.Concrete

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = StateT (IntMap n) (Except (InterpretError n))

runM :: IntMap n -> M n a -> Either (InterpretError n) a
runM st p = runExcept (evalStateT p st)

addBinding :: Ref -> n -> M n ()
addBinding (NumVar var) val = modify $ \xs -> IntMap.insert var val xs
addBinding (BoolVar var) val = modify $ \xs -> IntMap.insert var val xs

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

instance GaloisField n => Interpret Val n where
  interp (Number n) = return (fromIntegral n)
  interp (Boolean b) = interp b
  interp Unit = return zero

instance GaloisField n => Interpret Expr n where
  interp expr = case expr of
    Val val -> interp val
    Var (NumVar n) -> lookupVar n
    Var (BoolVar n) -> lookupVar n
    -- Var (UnitVar n) -> lookupVar n
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
    If b x y -> do
      b' <- interp b
      case b' of
        0 -> interp y
        _ -> interp x
    ToBool x -> interp x
    ToNum x -> interp x

--------------------------------------------------------------------------------

interpretElaborated2 :: (GaloisField n, Bounded n, Integral n) => Elaborated -> [n] -> Either (InterpretError n) (Maybe n)
interpretElaborated2 (Elaborated expr comp) inputs = runM bindings $ do
  -- interpret the assignments first
  forM_ (compNumAsgns comp) $ \(Assignment var e) -> do
    value <- interp e
    addBinding var value

  forM_ (compBoolAsgns comp) $ \(Assignment var e) -> do
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
  if isOfUnit expr
    then return Nothing
    else Just <$> interp expr
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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Interpret (interpret) where

import Control.Monad.Except
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Semiring (Semiring (..))
import Keelung.Monad (Assignment (..), Elaborated (..))
import Keelung.Syntax

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = StateT (IntMap n) (Except String)

runM :: IntMap n -> M n a -> Either String a
runM st p = runExcept (evalStateT p st)

addBinding :: Int -> n -> M n ()
addBinding var val = modify $ \xs -> IntMap.insert var val xs

lookupVar :: Show n => Int -> M n n
lookupVar var = do
  bindings <- get
  case IntMap.lookup var bindings of
    Nothing ->
      throwError $
        "unbound var " ++ show var
          ++ " in environment "
          ++ show bindings
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

--------------------------------------------------------------------------------

interpret :: GaloisField n => Elaborated n ty -> [n] -> Either String n
interpret (Elaborated _ inputVars expr numAssignments boolAssignments) inputs = runM bindings $ do
  -- interpret the assignments first
  forM_ numAssignments $ \(Assignment (Variable var) e) -> do
    value <- interp e
    addBinding var value

  forM_ boolAssignments $ \(Assignment (Variable var) e) -> do
    value <- interp e
    addBinding var value

  -- and then the expression
  interp expr
  where
    bindings = IntMap.fromAscList $ zip (IntSet.toAscList inputVars) inputs
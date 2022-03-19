{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}

module Keelung.Syntax.Untyped
  ( Op (..),
    Expr (..),
    Assignment (..),
    Erase,
    eraseType,
    eraseTypeFromAssignments,
  )
where

import Control.Monad.Writer
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import qualified Keelung.Monad as T
import qualified Keelung.Syntax as T
import Keelung.Syntax.Common

--------------------------------------------------------------------------------

-- Binary operators
data Op
  = Add
  | Sub
  | Mul
  | Div
  | And
  | Or
  | Xor
  | Eq
  | BEq
  deriving (Eq)

-- See if an operator is associative, so that we can chain them together
isAssoc :: Op -> Bool
isAssoc op = case op of
  Add -> True
  Sub -> False
  Mul -> True
  Div -> False
  And -> True
  Or -> True
  Xor -> True
  Eq -> True
  BEq -> True

--------------------------------------------------------------------------------

-- | Untyped expression
data Expr n
  = Var Var
  | Val n
  | BinOp Op [Expr n]
  | IfThenElse (Expr n) (Expr n) (Expr n)
  deriving (Eq, Functor)

instance Num n => Num (Expr n) where
  x + y = BinOp Add [x, y]
  x - y = BinOp Sub [x, y]
  x * y = BinOp Mul [x, y]
  abs = id
  signum = const 1
  fromInteger = Val . fromInteger

instance Show n => Show (Expr n) where
  showsPrec prec expr = case expr of
    Val val -> shows val
    Var var -> shows var
    BinOp op operands -> case op of
      Add -> chain " + " 6
      Sub -> chain " - " 6
      Mul -> chain " * " 7
      Div -> chain " / " 7
      And -> chain " ∧ " 3
      Or -> chain " ∨ " 2
      Xor -> chain " ⊕ " 4
      Eq -> chain " = " 5
      BEq -> chain " = " 5
      where
        chain :: String -> Int -> String -> String
        chain delim n = showParen (prec > n) $ mconcat $ List.intersperse (showString delim) (map (showsPrec (succ n)) operands)
    IfThenElse p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y

--------------------------------------------------------------------------------

data Assignment n = Assignment Var (Expr n)

instance Show n => Show (Assignment n) where
  show (Assignment var expr) = show var <> " := " <> show expr

instance Functor Assignment where
  fmap f (Assignment var expr) = Assignment var (fmap f expr)

--------------------------------------------------------------------------------

-- monad for collecting boolean vars along the way
type M = Writer IntSet

eraseType :: (Erase ty, Num n) => T.Expr ty n -> (Expr n, IntSet)
eraseType = runWriter . eraseExpr

eraseTypeFromAssignments :: (Erase ty, Num n) => [T.Assignment ty n] -> ([Assignment n], IntSet)
eraseTypeFromAssignments = runWriter . mapM eraseAssignment

--------------------------------------------------------------------------------

-- for stealing type info in runtime from the typeclass dictionary
class Erase ty where
  eraseExpr :: Num n => T.Expr ty n -> M (Expr n)
  eraseAssignment :: Num n => T.Assignment ty n -> M (Assignment n)

instance Erase 'T.Num where
  eraseExpr expr = case expr of
    T.Val val -> case val of
      (T.Number n) -> return (Val n)
    T.Var _ (T.Variable var) -> return (Var var)
    T.Add x y -> chainExprs Add <$> eraseExpr x <*> eraseExpr y
    T.Sub x y -> chainExprs Sub <$> eraseExpr x <*> eraseExpr y
    T.Mul x y -> chainExprs Mul <$> eraseExpr x <*> eraseExpr y
    T.Div x y -> chainExprs Div <$> eraseExpr x <*> eraseExpr y
    T.IfThenElse b x y -> IfThenElse <$> eraseExpr b <*> eraseExpr x <*> eraseExpr y
  eraseAssignment (T.Assignment (T.Variable var) expr) = Assignment var <$> eraseExpr expr

instance Erase 'T.Bool where
  eraseExpr expr = case expr of
    T.Val val -> case val of
      (T.Boolean True) -> return (Val 1)
      (T.Boolean False) -> return (Val 0)
    T.Var _ (T.Variable var) -> do
      tell (IntSet.singleton var)
      return (Var var)
    T.Eq x y -> chainExprs Eq <$> eraseExpr x <*> eraseExpr y
    T.And x y -> chainExprs And <$> eraseExpr x <*> eraseExpr y
    T.Or x y -> chainExprs Or <$> eraseExpr x <*> eraseExpr y
    T.Xor x y -> chainExprs Xor <$> eraseExpr x <*> eraseExpr y
    T.BEq x y -> chainExprs BEq <$> eraseExpr x <*> eraseExpr y
    T.IfThenElse b x y -> IfThenElse <$> eraseExpr b <*> eraseExpr x <*> eraseExpr y
  eraseAssignment (T.Assignment (T.Variable var) expr) = do
    tell (IntSet.singleton var)
    Assignment var <$> eraseExpr expr

-- Flatten and chain expressions together when possible
chainExprs :: Op -> Expr n -> Expr n -> Expr n
chainExprs op x y = case (x, y) of
  (BinOp op1 xs, BinOp op2 ys)
    | op1 == op2 && op2 == op && isAssoc op ->
      -- chaining `op`, `op1`, and `op2`
      BinOp op (xs ++ ys)
  (BinOp op1 xs, _)
    | op1 == op && isAssoc op ->
      -- chaining `op` and `op1`
      BinOp op (xs ++ [y])
  (_, BinOp op2 ys)
    | op2 == op && isAssoc op ->
      -- chaining `op` and `op2`
      BinOp op (x : ys)
  -- there's nothing left we can do
  _ -> BinOp op [x, y]
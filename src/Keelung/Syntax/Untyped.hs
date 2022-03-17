{-# LANGUAGE GADTs #-}

module Keelung.Syntax.Untyped where

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
  deriving (Eq)

instance Num n => Num (Expr n) where
  x + y = BinOp Add [x, y]
  x - y = BinOp Sub [x, y]
  x * y = BinOp Mul [x, y]
  abs = id
  signum = const 1
  fromInteger = Val . fromInteger

--------------------------------------------------------------------------------

eraseType :: Num n => T.Expr n ty -> Expr n
eraseType expr = case expr of
  T.Val val -> case val of
    (T.Number n) -> Val n
    (T.Boolean True) -> Val 1
    (T.Boolean False) -> Val 0
  T.Var _ (T.Variable n) -> Var n
  T.Add x y -> chainExprs Add (eraseType x) (eraseType y)
  T.Sub x y -> chainExprs Sub (eraseType x) (eraseType y)
  T.Mul x y -> chainExprs Mul (eraseType x) (eraseType y)
  T.Div x y -> chainExprs Div (eraseType x) (eraseType y)
  T.Eq x y -> chainExprs Eq (eraseType x) (eraseType y)
  T.And x y -> chainExprs And (eraseType x) (eraseType y)
  T.Or x y -> chainExprs Or (eraseType x) (eraseType y)
  T.Xor x y -> chainExprs Xor (eraseType x) (eraseType y)
  T.BEq x y -> chainExprs BEq (eraseType x) (eraseType y)
  T.IfThenElse b x y -> IfThenElse (eraseType b) (eraseType x) (eraseType y)

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
{-# LANGUAGE GADTs #-}

module Keelung.Compiler.Syntax.Typed where 

import Keelung.Syntax
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

--------------------------------------------------------------------------------

-- calculate the "size" of an expression
sizeOfExpr :: Expr ty n -> Int
sizeOfExpr expr = case expr of
  Val _ -> 1
  Var _ -> 1
  Add x y -> 1 + sizeOfExpr x + sizeOfExpr y
  Sub x y -> 1 + sizeOfExpr x + sizeOfExpr y
  Mul x y -> 1 + sizeOfExpr x + sizeOfExpr y
  Div x y -> 1 + sizeOfExpr x + sizeOfExpr y
  Eq x y -> 1 + sizeOfExpr x + sizeOfExpr y
  And x y -> 1 + sizeOfExpr x + sizeOfExpr y
  Or x y -> 1 + sizeOfExpr x + sizeOfExpr y
  Xor x y -> 1 + sizeOfExpr x + sizeOfExpr y
  BEq x y -> 1 + sizeOfExpr x + sizeOfExpr y
  IfThenElse x y z -> 1 + sizeOfExpr x + sizeOfExpr y + sizeOfExpr z
  ToBool x -> 1 + sizeOfExpr x
  ToNum x -> 1 + sizeOfExpr x

-- collect free variables of an expression
freeVars :: Expr ty n -> IntSet
freeVars expr = case expr of
  Val _ -> mempty
  Var (Variable n) -> IntSet.singleton n
  Add x y -> freeVars x <> freeVars y
  Sub x y -> freeVars x <> freeVars y
  Mul x y -> freeVars x <> freeVars y
  Div x y -> freeVars x <> freeVars y
  Eq x y -> freeVars x <> freeVars y
  And x y -> freeVars x <> freeVars y
  Or x y -> freeVars x <> freeVars y
  Xor x y -> freeVars x <> freeVars y
  BEq x y -> freeVars x <> freeVars y
  IfThenElse x y z -> freeVars x <> freeVars y <> freeVars z
  ToBool x -> freeVars x
  ToNum x -> freeVars x

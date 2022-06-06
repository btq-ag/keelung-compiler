{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Keelung.Compiler.Syntax.Untyped2
  ( eraseType,
    sizeOfExpr,
    freeVars,
  )
where

import Control.Monad.State.Strict
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Sequence ((<|), (|>))
import qualified Data.Sequence as Seq
import Keelung.Compiler.Syntax.Untyped
import qualified Keelung.Syntax.Unkinded as T

--------------------------------------------------------------------------------

-- monad for collecting boolean vars along the way
type M = State IntSet

eraseType :: Num n => T.Elaborated n -> TypeErased n
eraseType (T.Elaborated expr comp) =
  let T.Computation nextVar _nextAddr inputVars _heap numAsgns boolAsgns assertions = comp
      ((erasedExpr', erasedAssignments', erasedAssertions'), booleanVars) = flip runState mempty $ do
        expr' <- eraseExprM expr
        numAssignments' <- mapM eraseAssignment numAsgns
        boolAssignments' <- mapM eraseAssignment boolAsgns
        let assignments = numAssignments' <> boolAssignments'
        assertions' <- mapM eraseExpr assertions
        return (expr', assignments, assertions')
   in TypeErased
        { erasedExpr = erasedExpr',
          erasedAssertions = erasedAssertions',
          erasedAssignments = erasedAssignments',
          erasedNumOfVars = nextVar,
          erasedInputVars = inputVars,
          erasedBooleanVars = booleanVars
        }

eraseExpr :: Num n => T.Expr n -> M (Expr n)
eraseExpr expr = case expr of
  T.Val val -> case val of
    (T.Number n) -> return (Val n)
    (T.Boolean False) -> return (Val 0)
    (T.Boolean True) -> return (Val 1)
    T.Unit -> return (Val 0) -- TODO: revise this
  T.Var var -> case var of
    T.NumVar n -> return (Var n)
    T.BoolVar n -> do
      modify' (IntSet.insert n) -- keep track of all boolean variables
      return (Var n)
    T.UnitVar n -> return (Var n)
  T.Add x y -> chainExprs Add <$> eraseExpr x <*> eraseExpr y
  T.Sub x y -> chainExprs Sub <$> eraseExpr x <*> eraseExpr y
  T.Mul x y -> chainExprs Mul <$> eraseExpr x <*> eraseExpr y
  T.Div x y -> chainExprs Div <$> eraseExpr x <*> eraseExpr y
  T.Eq x y -> chainExprs Eq <$> eraseExpr x <*> eraseExpr y
  T.And x y -> chainExprs And <$> eraseExpr x <*> eraseExpr y
  T.Or x y -> chainExprs Or <$> eraseExpr x <*> eraseExpr y
  T.Xor x y -> chainExprs Xor <$> eraseExpr x <*> eraseExpr y
  T.BEq x y -> chainExprs BEq <$> eraseExpr x <*> eraseExpr y
  T.IfThenElse b x y -> IfThenElse <$> eraseExpr b <*> eraseExpr x <*> eraseExpr y
  T.ToBool x -> eraseExpr x
  T.ToNum x -> eraseExpr x

-- | Like `eraseExpr` but returns `Nothing` on `T.Unit`
eraseExprM :: Num n => T.Expr n -> M (Maybe (Expr n))
eraseExprM expr = case expr of
  T.Val val -> case val of
    (T.Number n) -> return $ Just (Val n)
    (T.Boolean False) -> return $ Just (Val 0)
    (T.Boolean True) -> return $ Just (Val 1)
    T.Unit -> return Nothing
  T.Var var -> case var of
    T.NumVar n -> return $ Just (Var n)
    T.BoolVar n -> do
      modify' (IntSet.insert n) -- keep track of all boolean variables
      return $ Just (Var n)
    T.UnitVar n -> return $ Just (Var n)
  T.Add x y -> Just <$> (chainExprs Add <$> eraseExpr x <*> eraseExpr y)
  T.Sub x y -> Just <$> (chainExprs Sub <$> eraseExpr x <*> eraseExpr y)
  T.Mul x y -> Just <$> (chainExprs Mul <$> eraseExpr x <*> eraseExpr y)
  T.Div x y -> Just <$> (chainExprs Div <$> eraseExpr x <*> eraseExpr y)
  T.Eq x y -> Just <$> (chainExprs Eq <$> eraseExpr x <*> eraseExpr y)
  T.And x y -> Just <$> (chainExprs And <$> eraseExpr x <*> eraseExpr y)
  T.Or x y -> Just <$> (chainExprs Or <$> eraseExpr x <*> eraseExpr y)
  T.Xor x y -> Just <$> (chainExprs Xor <$> eraseExpr x <*> eraseExpr y)
  T.BEq x y -> Just <$> (chainExprs BEq <$> eraseExpr x <*> eraseExpr y)
  T.IfThenElse b x y -> Just <$> (IfThenElse <$> eraseExpr b <*> eraseExpr x <*> eraseExpr y)
  T.ToBool x -> eraseExprM x
  T.ToNum x -> eraseExprM x

eraseAssignment :: Num n => T.Assignment n -> M (Assignment n)
eraseAssignment (T.Assignment (T.NumVar n) expr) = Assignment n <$> eraseExpr expr
eraseAssignment (T.Assignment (T.BoolVar n) expr) = do 
  modify' (IntSet.insert n) -- keep track of all boolean variables
  Assignment n <$> eraseExpr expr
eraseAssignment (T.Assignment (T.UnitVar n) expr) = Assignment n <$> eraseExpr expr

-- Flatten and chain expressions together when possible
chainExprs :: Op -> Expr n -> Expr n -> Expr n
chainExprs op x y = case (x, y) of
  (BinOp op1 xs, BinOp op2 ys)
    | op1 == op2 && op2 == op && isAssoc op ->
      -- chaining `op`, `op1`, and `op2`
      BinOp op (xs <> ys)
  (BinOp op1 xs, _)
    | op1 == op && isAssoc op ->
      -- chaining `op` and `op1`
      BinOp op (xs |> y)
  (_, BinOp op2 ys)
    | op2 == op && isAssoc op ->
      -- chaining `op` and `op2`
      BinOp op (x <| ys)
  -- there's nothing left we can do
  _ -> BinOp op (Seq.fromList [x, y])

-- collect free variables of an expression
freeVars :: T.Expr n -> IntSet
freeVars expr = case expr of
  T.Val _ -> mempty
  T.Var (T.NumVar n) -> IntSet.singleton n
  T.Var (T.BoolVar n) -> IntSet.singleton n
  T.Var (T.UnitVar n) -> IntSet.singleton n
  T.Add x y -> freeVars x <> freeVars y
  T.Sub x y -> freeVars x <> freeVars y
  T.Mul x y -> freeVars x <> freeVars y
  T.Div x y -> freeVars x <> freeVars y
  T.Eq x y -> freeVars x <> freeVars y
  T.And x y -> freeVars x <> freeVars y
  T.Or x y -> freeVars x <> freeVars y
  T.Xor x y -> freeVars x <> freeVars y
  T.BEq x y -> freeVars x <> freeVars y
  T.IfThenElse x y z -> freeVars x <> freeVars y <> freeVars z
  T.ToBool x -> freeVars x
  T.ToNum x -> freeVars x

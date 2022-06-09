{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}

module Keelung.Compiler.Syntax.Untyped2
  ( Op (..),
    Expr (..),
    TypeErased (..),
    Assignment (..),
    eraseType,
    sizeOfExpr,
    isAssoc,
  )
where

import Control.Monad.State
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Sequence (Seq (..), (<|), (|>))
import qualified Data.Sequence as Seq
import Keelung.Field
import Keelung.Syntax (Var)
import qualified Keelung.Syntax.Concrete as T

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
  | NEq
  | Eq
  | BEq
  deriving (Eq, Show)

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
  NEq -> True
  Eq -> True
  BEq -> True

--------------------------------------------------------------------------------

-- | Untyped expression
data Expr n
  = Var Var
  | Val n
  | BinOp Op (Seq (Expr n))
  | IfThenElse (Expr n) (Expr n) (Expr n)
  deriving (Eq, Functor)

instance Num n => Num (Expr n) where
  x + y = BinOp Add (Seq.fromList [x, y])
  x - y = BinOp Sub (Seq.fromList [x, y])
  x * y = BinOp Mul (Seq.fromList [x, y])
  abs = id
  signum = const 1
  fromInteger = Val . fromInteger

instance Show n => Show (Expr n) where
  showsPrec prec expr = case expr of
    Val val -> shows val
    Var var -> showString "$" . shows var
    BinOp op operands -> case op of
      Add -> chain " + " 6 operands
      Sub -> chain " - " 6 operands
      Mul -> chain " * " 7 operands
      Div -> chain " / " 7 operands
      And -> chain " ∧ " 3 operands
      Or -> chain " ∨ " 2 operands
      Xor -> chain " ⊕ " 4 operands
      NEq -> chain " != " 5 operands
      Eq -> chain " == " 5 operands
      BEq -> chain " == " 5 operands
      where
        chain :: Show n => String -> Int -> Seq (Expr n) -> String -> String
        chain delim n xs = showParen (prec > n) $ go delim n xs

        go :: Show n => String -> Int -> Seq (Expr n) -> String -> String
        go _ _ Empty = showString ""
        go _ n (x :<| Empty) = showsPrec (succ n) x
        go delim n (x :<| xs) = showsPrec (succ n) x . showString delim . go delim n xs
    IfThenElse p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y

-- calculate the "size" of an expression
sizeOfExpr :: Expr n -> Int
sizeOfExpr expr = case expr of
  Val _ -> 1
  Var _ -> 1
  BinOp _ operands -> sum (fmap sizeOfExpr operands) + (length operands - 1)
  IfThenElse x y z -> 1 + sizeOfExpr x + sizeOfExpr y + sizeOfExpr z

--------------------------------------------------------------------------------

data Assignment n = Assignment Var (Expr n)

instance Show n => Show (Assignment n) where
  show (Assignment var expr) = "$" <> show var <> " := " <> show expr

instance Functor Assignment where
  fmap f (Assignment var expr) = Assignment var (fmap f expr)

--------------------------------------------------------------------------------

-- | The result after type erasure
data TypeErased =
  -- forall n.
  -- (AcceptedField n, Show n, Bounded n, Integral n, Fractional n) =>
  TypeErased
  { -- | The expression after type erasure
    erasedExpr :: !(Maybe (Expr Integer)),
    -- | Assertions after type erasure
    erasedAssertions :: ![Expr Integer],
    -- | Assignments after type erasure
    erasedAssignments :: ![Assignment Integer],
    -- | Number of variables
    erasedNumOfVars :: !Int,
    -- | Variables marked as inputs
    erasedInputVars :: !IntSet,
    -- | Variables that are boolean
    erasedBooleanVars :: !IntSet,
    -- | Field type of the numbers
    erasedFieldType :: !FieldType
  }

instance Show TypeErased where
  show (TypeErased expr assertions assignments numOfVars inputVars boolVars fieldType) =
    "TypeErased {\n\
    \  expression: "
      <> show (fmap (fmap (display fieldType)) expr)
      <> "\n"
      <> ( if length assignments < 20
             then "  assignments:\n" <> show (map (fmap (display fieldType)) assignments) <> "\n"
             else ""
         )
      <> ( if length assertions < 20
             then "  assertions:\n" <> show assertions <> "\n"
             else ""
         )
      <> "  number of variables: "
      <> show numOfVars
      <> "\n\
         \  number of input variables: "
      <> show (IntSet.size inputVars)
      <> "\n  boolean variable: "
      <> show boolVars
      <> "\n  field type: "
      <> show fieldType
      <> "\n\
         \}"

--------------------------------------------------------------------------------

-- monad for collecting boolean vars along the way
type M = State IntSet

eraseType :: T.Elaborated -> TypeErased
eraseType (T.Elaborated expr comp) =
  let T.Computation nextVar _nextAddr inputVars _heap numAsgns boolAsgns assertions fieldType = comp
   in flip evalState mempty $ do
        expr' <- eraseExprM expr
        numAssignments' <- mapM eraseAssignment numAsgns
        boolAssignments' <- mapM eraseAssignment boolAsgns
        let assignments = numAssignments' <> boolAssignments'
        assertions' <- mapM eraseExpr assertions
        booleanVars <- get
        return $
          TypeErased
            { erasedExpr = expr',
              erasedAssertions = assertions',
              erasedAssignments = assignments,
              erasedNumOfVars = nextVar,
              erasedInputVars = inputVars,
              erasedBooleanVars = booleanVars,
              erasedFieldType = fieldType
            }

eraseExpr :: Num n => T.Expr -> M (Expr n)
eraseExpr expr = case expr of
  T.Val val -> case val of
    (T.Number n) -> return (Val (fromIntegral n))
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
eraseExprM :: Num n => T.Expr -> M (Maybe (Expr n))
eraseExprM expr = case expr of
  T.Val val -> case val of
    (T.Number n) -> return $ Just (Val (fromInteger n))
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

eraseAssignment :: Num n => T.Assignment -> M (Assignment n)
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

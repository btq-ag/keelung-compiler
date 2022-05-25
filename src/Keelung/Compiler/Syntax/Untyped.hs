{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}

module Keelung.Compiler.Syntax.Untyped
  ( Op (..),
    Expr (..),
    Erase,
    TypeErased (..),
    Assignment (..),
    eraseType,
    sizeOfExpr,
  )
where

import Control.Monad.State.Strict
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Sequence (Seq (..), (<|), (|>))
import qualified Data.Sequence as Seq
import qualified Keelung.Monad as T
import qualified Keelung.Syntax as T
import Keelung.Syntax (Var)
import Keelung.Field (N(..))

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

-- monad for collecting boolean vars along the way
type M = State IntSet

--------------------------------------------------------------------------------

-- | The result after type erasure
data TypeErased n = TypeErased
  { -- | The expression after type erasure
    erasedExpr :: !(Maybe (Expr n)),
    -- | Assertions after type erasure
    erasedAssertions :: ![Expr n],
    -- | Assignments after type erasure
    erasedAssignments :: ![Assignment n],
    -- | Number of variables
    erasedNumOfVars :: !Int,
    -- | Variables marked as inputs
    erasedInputVars :: !IntSet,
    -- | Variables that are boolean
    erasedBooleanVars :: !IntSet
  }

instance (Show n, Bounded n, Integral n, Fractional n) => Show (TypeErased n) where
  show (TypeErased expr assertions assignments numOfVars inputVars boolVars) =
    "TypeErased {\n\
    \  expression: "
      <> show (fmap (fmap N) expr)
      <> "\n"
      <> ( if length assignments < 20
             then "  assignments:\n" <> show (map (fmap N) assignments) <> "\n"
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
      <> "\n\
         \}"

eraseType :: (Erase ty, Num n) => T.Elaborated ty n -> TypeErased n
eraseType (T.Elaborated expr comp) =
  let T.Computation nextVar _nextAddr inputVars _heap numAsgns boolAsgns assertions = comp
      ((erasedExpr', erasedAssignments', erasedAssertions'), booleanVars) = flip runState mempty $ do
        expr' <- mapM eraseExpr expr
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

-- for stealing type info in runtime from the typeclass dictionary
class Erase ty where
  eraseExpr :: Num n => T.Expr ty n -> M (Expr n)
  eraseAssignment :: Num n => T.Assignment ty n -> M (Assignment n)

instance Erase 'T.Unit where
  eraseExpr expr = case expr of
    T.Val val -> case val of T.UnitVal -> return (Val 0)
    T.Var (T.Variable var) -> return (Var var)
    T.IfThenElse b x y -> IfThenElse <$> eraseExpr b <*> eraseExpr x <*> eraseExpr y
  eraseAssignment (T.Assignment (T.Variable var) expr) = Assignment var <$> eraseExpr expr

instance Erase 'T.Num where
  eraseExpr expr = case expr of
    T.Val val -> case val of
      (T.Number n) -> return (Val n)
    T.Var (T.Variable var) -> return (Var var)
    T.Add x y -> chainExprs Add <$> eraseExpr x <*> eraseExpr y
    T.Sub x y -> chainExprs Sub <$> eraseExpr x <*> eraseExpr y
    T.Mul x y -> chainExprs Mul <$> eraseExpr x <*> eraseExpr y
    T.Div x y -> chainExprs Div <$> eraseExpr x <*> eraseExpr y
    T.IfThenElse b x y -> IfThenElse <$> eraseExpr b <*> eraseExpr x <*> eraseExpr y
    T.ToNum x -> eraseExpr x
  eraseAssignment (T.Assignment (T.Variable var) expr) = Assignment var <$> eraseExpr expr

instance Erase 'T.Bool where
  eraseExpr expr = case expr of
    T.Val val -> case val of
      (T.Boolean True) -> return (Val 1)
      (T.Boolean False) -> return (Val 0)
    T.Var (T.Variable var) -> do
      modify' $ \st -> IntSet.insert var st
      return (Var var)
    T.Eq x y -> chainExprs Eq <$> eraseExpr x <*> eraseExpr y
    T.And x y -> chainExprs And <$> eraseExpr x <*> eraseExpr y
    T.Or x y -> chainExprs Or <$> eraseExpr x <*> eraseExpr y
    T.Xor x y -> chainExprs Xor <$> eraseExpr x <*> eraseExpr y
    T.BEq x y -> chainExprs BEq <$> eraseExpr x <*> eraseExpr y
    T.IfThenElse b x y -> IfThenElse <$> eraseExpr b <*> eraseExpr x <*> eraseExpr y
    T.ToBool x -> eraseExpr x
  eraseAssignment (T.Assignment (T.Variable var) expr) = do
    modify' $ \st -> IntSet.insert var st
    Assignment var <$> eraseExpr expr

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
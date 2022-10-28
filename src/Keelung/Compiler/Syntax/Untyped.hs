{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}

module Keelung.Compiler.Syntax.Untyped
  ( Op (..),
    BinaryOp (..),
    Expr (..),
    TypeErased (..),
    Assignment (..),
    sizeOfExpr,
  )
where

import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.List as List
import Data.Sequence (Seq (..))
import Keelung.Field (N (..))
import Keelung.Syntax.VarCounters
import Keelung.Types (Var)

--------------------------------------------------------------------------------

-- N-ary operators
data Op
  = Add
  | Mul
  | And
  | Or
  | Xor
  | NEq
  | Eq
  | BEq
  deriving (Eq, Show)

-- Binary operators
data BinaryOp = Sub | Div
  deriving (Eq, Show)

--------------------------------------------------------------------------------

-- | Untyped expression
data Expr n
  = Val n
  | Var Var
  | -- Binary operators with only 2 operands
    BinaryOp BinaryOp (Expr n) (Expr n)
  | -- N-Ary operators with >= 2 operands
    NAryOp Op (Expr n) (Expr n) (Seq (Expr n))
  | If (Expr n) (Expr n) (Expr n)
  deriving (Eq, Functor)

instance Num n => Num (Expr n) where
  x + y = NAryOp Add x y Empty
  x - y = BinaryOp Sub x y
  x * y = NAryOp Mul x y Empty
  abs = id
  signum = const 1
  fromInteger = Val . fromInteger

instance Show n => Show (Expr n) where
  showsPrec prec expr =
    let chain :: Show n => String -> Int -> Seq (Expr n) -> String -> String
        chain delim n = showParen (prec > n) . go delim n
        go :: Show n => String -> Int -> Seq (Expr n) -> String -> String
        go _ _ Empty = showString ""
        go _ n (x :<| Empty) = showsPrec (succ n) x
        go delim n (x :<| xs') = showsPrec (succ n) x . showString delim . go delim n xs'
     in case expr of
          Var var -> showString "$" . shows var
          Val val -> shows val
          NAryOp op x0 x1 xs -> case op of
            Add -> chain " + " 6 $ x0 :<| x1 :<| xs
            Mul -> chain " * " 7 $ x0 :<| x1 :<| xs
            And -> chain " ∧ " 3 $ x0 :<| x1 :<| xs
            Or -> chain " ∨ " 2 $ x0 :<| x1 :<| xs
            Xor -> chain " ⊕ " 4 $ x0 :<| x1 :<| xs
            NEq -> chain " != " 5 $ x0 :<| x1 :<| xs
            Eq -> chain " == " 5 $ x0 :<| x1 :<| xs
            BEq -> chain " == " 5 $ x0 :<| x1 :<| xs
          BinaryOp op x0 x1 -> case op of
            Sub -> chain " - " 6 $ x0 :<| x1 :<| Empty
            Div -> chain " / " 7 $ x0 :<| x1 :<| Empty
          If p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y

-- | Calculate the "size" of an expression for benchmarking
sizeOfExpr :: Expr n -> Int
sizeOfExpr expr = case expr of
  Val _ -> 1
  Var _ -> 1
  NAryOp _ x0 x1 xs ->
    let operands = x0 :<| x1 :<| xs
     in sum (fmap sizeOfExpr operands) + (length operands - 1)
  BinaryOp _ x0 x1 -> sizeOfExpr x0 + sizeOfExpr x1 + 1
  If x y z -> 1 + sizeOfExpr x + sizeOfExpr y + sizeOfExpr z

--------------------------------------------------------------------------------

data Assignment n = Assignment Var (Expr n)

instance Show n => Show (Assignment n) where
  show (Assignment var expr) = "$" <> show var <> " := " <> show expr

instance Functor Assignment where
  fmap f (Assignment var expr) = Assignment var (fmap f expr)

--------------------------------------------------------------------------------

-- | The result after type erasure
data TypeErased n = TypeErased
  { -- | The expression after type erasure
    erasedExpr :: ![Expr n],
    -- | Variable bookkeepung
    erasedVarCounters :: !VarCounters,
    -- | Assertions after type erasure
    erasedAssertions :: ![Expr n],
    -- | Assignments after type erasure
    erasedAssignments :: ![Assignment n],
    -- | Pairs of Number input variables and their binary representation
    erasedBinReps :: IntMap (Var, Int)
  }

instance (GaloisField n, Integral n) => Show (TypeErased n) where
  show (TypeErased expr counters assertions assignments binReps) =
    "TypeErased {\n\
    \  expression: "
      <> show (fmap (fmap N) expr)
      <> "\n"
      <> ( if length assignments < 20
             then "  assignments:\n    " <> show (map (fmap N) assignments) <> "\n"
             else ""
         )
      <> ( if length assertions < 20
             then "  assertions:\n    " <> show assertions <> "\n"
             else ""
         )
      <> indent (show counters)
      <> "  Boolean variables: $"
      <> show (fst (boolVarsRange counters))
      <> " .. $"
      <> show (snd (boolVarsRange counters) - 1)
      <> "\n"
      <> showBinReps
      <> "\n\
         \}"
    where
      showBinReps =
        if IntMap.null binReps
          then ""
          else
            "  Binary representation of input variables: "
              <> showList'
                ( map
                    ( \(v, (b, n)) ->
                        "$" <> show v <> " = $" <> show b <> " + 2$" <> show (b + 1) <> " + ... + 2^" <> show (n - 1) <> "$" <> show (b + n - 1)
                    )
                    (IntMap.toList binReps)
                )
              <> "\n"

      showList' ys = "[" <> List.intercalate ", " ys <> "]"

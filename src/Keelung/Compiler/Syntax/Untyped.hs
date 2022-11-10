{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}

module Keelung.Compiler.Syntax.Untyped
  ( Op (..),
    BitWidth (..),
    bitWidthOf,
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

data BitWidth = Number | Boolean | UInt Int
  deriving (Eq, Ord, Show)

-- | Untyped expression
data Expr n
  = Val BitWidth n
  | Var BitWidth Var
  | Rotate BitWidth Int (Expr n)
  | -- Binary operators with only 2 operands
    BinaryOp BitWidth BinaryOp (Expr n) (Expr n)
  | -- N-Ary operators with >= 2 operands
    NAryOp BitWidth Op (Expr n) (Expr n) (Seq (Expr n))
  | If BitWidth (Expr n) (Expr n) (Expr n)
  deriving (Eq, Functor)

instance Num n => Num (Expr n) where
  x + y = NAryOp (bitWidthOf x) Add x y Empty
  x - y = BinaryOp (bitWidthOf x) Sub x y
  x * y = NAryOp (bitWidthOf x) Mul x y Empty
  abs = id
  signum = const 1
  fromInteger = Val Number . fromInteger -- NOTE: this "Number" is probably wrong

instance Show n => Show (Expr n) where
  showsPrec prec expr =
    let chain :: Show n => String -> Int -> Seq (Expr n) -> String -> String
        chain delim n = showParen (prec > n) . go delim n
        go :: Show n => String -> Int -> Seq (Expr n) -> String -> String
        go _ _ Empty = showString ""
        go _ n (x :<| Empty) = showsPrec (succ n) x
        go delim n (x :<| xs') = showsPrec (succ n) x . showString delim . go delim n xs'
     in case expr of
          Var _ var -> showString "$" . shows var
          Val _ val -> shows val
          Rotate _ n x -> showString "ROTATE " . shows n . showString " " . showsPrec 11 x
          NAryOp _ op x0 x1 xs -> case op of
            Add -> chain " + " 6 $ x0 :<| x1 :<| xs
            Mul -> chain " * " 7 $ x0 :<| x1 :<| xs
            And -> chain " ∧ " 3 $ x0 :<| x1 :<| xs
            Or -> chain " ∨ " 2 $ x0 :<| x1 :<| xs
            Xor -> chain " ⊕ " 4 $ x0 :<| x1 :<| xs
            NEq -> chain " != " 5 $ x0 :<| x1 :<| xs
            Eq -> chain " == " 5 $ x0 :<| x1 :<| xs
            BEq -> chain " == " 5 $ x0 :<| x1 :<| xs
          BinaryOp _ op x0 x1 -> case op of
            Sub -> chain " - " 6 $ x0 :<| x1 :<| Empty
            Div -> chain " / " 7 $ x0 :<| x1 :<| Empty
          If _ p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y

-- | Calculate the "size" of an expression for benchmarking
sizeOfExpr :: Expr n -> Int
sizeOfExpr expr = case expr of
  Val _ _ -> 1
  Var _ _ -> 1
  Rotate _ _ x -> 1 + sizeOfExpr x
  NAryOp _ _ x0 x1 xs ->
    let operands = x0 :<| x1 :<| xs
     in sum (fmap sizeOfExpr operands) + (length operands - 1)
  BinaryOp _ _ x0 x1 -> sizeOfExpr x0 + sizeOfExpr x1 + 1
  If _ x y z -> 1 + sizeOfExpr x + sizeOfExpr y + sizeOfExpr z

bitWidthOf :: Expr n -> BitWidth
bitWidthOf expr = case expr of
  Val bw _ -> bw
  Var bw _ -> bw
  Rotate bw _ _ -> bw
  NAryOp bw _ _ _ _ -> bw
  BinaryOp bw _ _ _ -> bw
  If bw _ _ _ -> bw

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
    -- | Pairs of Number input variables and start index of binary representation
    --    [(inputIndex, binRepIndex)]
    erasedBinReps :: IntMap Var,
    -- | Pairs of custom input variables and start index of binary representation
    --    [(bitWidth,[(inputIndex, binRepIndex)])]
    erasedCustomBinReps :: IntMap (IntMap Var)
  }

instance (GaloisField n, Integral n) => Show (TypeErased n) where
  show (TypeErased expr counters assertions assignments numBinReps customBinReps) =
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
      <> showBinRepConstraints
      <> "\n\
         \}"
    where
      numBitWidth = getNumBitWidth counters
      totalBinRepConstraintSize = numInputVarSize counters + totalCustomInputSize counters
      showBinRepConstraints =
        if totalBinRepConstraintSize == 0
          then ""
          else
            "  Binary representation constriants (" <> show totalBinRepConstraintSize <> "):\n"
              <> unlines
                ( map
                    (uncurry (showBinRepConstraint numBitWidth))
                    (IntMap.toList numBinReps)
                    ++ concatMap
                      ( \(bitWidth, pairs) ->
                          map
                            (uncurry (showBinRepConstraint bitWidth))
                            (IntMap.toList pairs)
                      )
                      (IntMap.toList customBinReps)
                )
        where
          showBinRepConstraint 2 var binRep =
            "    $"
              <> show var
              <> " = $"
              <> show binRep
              <> " + 2$"
              <> show (binRep + 1)
          showBinRepConstraint 3 var binRep =
            "    $"
              <> show var
              <> " = $"
              <> show binRep
              <> " + 2$"
              <> show (binRep + 1)
              <> " + 4$"
              <> show (binRep + 2)
          showBinRepConstraint width var binRep =
            "    $"
              <> show var
              <> " = $"
              <> show binRep
              <> " + 2$"
              <> show (binRep + 1)
              <> " + ... + 2^"
              <> show (width - 1)
              <> "$"
              <> show (binRep + width - 1)

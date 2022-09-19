{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}

module Keelung.Compiler.Syntax.Untyped
  ( Op (..),
    Expr (..),
    TypeErased (..),
    Assignment (..),
    eraseType,
    sizeOfExpr,
    isAssoc,
  )
where

import Control.Monad.Reader
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Sequence (Seq (..), (<|), (|>))
import qualified Data.Sequence as Seq
import Keelung.Field (N (..))
import qualified Keelung.Syntax.Typed as T
import Keelung.Types (Var)

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
  | If (Expr n) (Expr n) (Expr n)
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
    If p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y

-- calculate the "size" of an expression
sizeOfExpr :: Expr n -> Int
sizeOfExpr expr = case expr of
  Val _ -> 1
  Var _ -> 1
  BinOp _ operands -> sum (fmap sizeOfExpr operands) + (length operands - 1)
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
    -- | Assertions after type erasure
    erasedAssertions :: ![Expr n],
    -- | Assignments after type erasure
    erasedAssignments :: ![Assignment n],
    -- | Number of variables
    erasedNumOfVars :: !Int,
    -- | Number of input variables (they are placed at the beginning of the variable list)
    erasedNumOfInputVars :: !Int,
    -- | Input variables that are boolean
    erasedBoolInputVars :: !IntSet
  }

instance (GaloisField n, Integral n) => Show (TypeErased n) where
  show (TypeErased expr assertions assignments numOfVars numOfInputVars boolVars) =
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
      <> show numOfInputVars
      <> "\n  boolean variable: "
      <> show boolVars
      <> "\n\
         \}"

--------------------------------------------------------------------------------

-- monad for collecting boolean vars along the way
type M = ReaderT Int (State IntSet)

runM :: Int -> M a -> (a, IntSet)
runM inputSize = flip runState IntSet.empty . flip runReaderT inputSize

eraseType :: GaloisField n => T.Elaborated -> TypeErased n
eraseType (T.Elaborated expr comp) =
  let T.Computation nextVar nextInputVar _nextAddr _heap numAsgns boolAsgns assertions = comp
      ((erasedExpr', erasedAssignments', erasedAssertions'), boolInputVars) =
        runM nextInputVar $ do
          expr' <- eraseExpr expr
          numAssignments' <- mapM eraseAssignment numAsgns
          boolAssignments' <- mapM eraseAssignment boolAsgns
          let assignments = numAssignments' <> boolAssignments'
          assertions' <- concat <$> mapM eraseExpr assertions
          return (expr', assignments, assertions')
   in TypeErased
        { erasedExpr = erasedExpr',
          erasedAssertions = erasedAssertions',
          erasedAssignments = erasedAssignments',
          erasedNumOfVars = nextInputVar + nextVar,
          erasedNumOfInputVars = nextInputVar,
          erasedBoolInputVars = boolInputVars
        }

eraseVal :: GaloisField n => T.Val -> M [Expr n]
eraseVal (T.Integer n) = return [Val (fromInteger n)]
eraseVal (T.Rational n) = return [Val (fromRational n)]
eraseVal (T.Boolean False) = return [Val 0]
eraseVal (T.Boolean True) = return [Val 1]
eraseVal T.Unit = return []

eraseRef' :: T.Ref -> M Int
eraseRef' ref = do
  inputSize <- ask
  case ref of
    T.NumVar n -> return (inputSize + n)
    T.NumInputVar n -> return n
    T.BoolVar n -> return (inputSize + n)
    T.BoolInputVar n -> do
      -- keep track of all boolean input variables
      -- so that we can later impose constraints on them (e.g. $A * $A = $A)
      modify' (IntSet.insert n) 
      return n

eraseRef :: GaloisField n => T.Ref -> M (Expr n)
eraseRef ref = Var <$> eraseRef' ref

-- eraseVal (T.Integer n) = return [Val (fromInteger n)]
-- eraseVal (T.Rational n) = return [Val (fromRational n)]
-- eraseVal (T.Boolean False) = return [Val 0]
-- eraseVal (T.Boolean True) = return [Val 1]
-- eraseVal T.Unit = return []

eraseExpr :: GaloisField n => T.Expr -> M [Expr n]
eraseExpr expr = case expr of
  T.Val val -> eraseVal val
  T.Var ref -> pure <$> eraseRef ref
  T.Array exprs -> do
    exprss <- mapM eraseExpr exprs
    return $ concat exprss
  T.Add x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprs Add (head xs) (head ys)]
  T.Sub x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprs Sub (head xs) (head ys)]
  T.Mul x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprs Mul (head xs) (head ys)]
  T.Div x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprs Div (head xs) (head ys)]
  T.Eq x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprs Eq (head xs) (head ys)]
  T.And x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprs And (head xs) (head ys)]
  T.Or x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprs Or (head xs) (head ys)]
  T.Xor x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprs Xor (head xs) (head ys)]
  T.BEq x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprs BEq (head xs) (head ys)]
  T.If b x y -> do
    bs <- eraseExpr b
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [If (head bs) (head xs) (head ys)]
  T.ToBool x -> eraseExpr x
  T.ToNum x -> eraseExpr x

eraseAssignment :: GaloisField n => T.Assignment -> M (Assignment n)
eraseAssignment (T.Assignment ref expr) = do
  var <- eraseRef' ref
  exprs <- eraseExpr expr
  return $ Assignment var (head exprs)

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

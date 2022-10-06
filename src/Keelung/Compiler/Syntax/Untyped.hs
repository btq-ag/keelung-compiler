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

-- | Calculate the "size" of an expression for benchmarking
sizeOfExpr :: Expr n -> Int
sizeOfExpr expr = case expr of
  Val _ -> 1
  Var _ -> 1
  BinOp _ operands -> sum (fmap sizeOfExpr operands) + (length operands - 1)
  If x y z -> 1 + sizeOfExpr x + sizeOfExpr y + sizeOfExpr z

-- | Calculate the "length" of an expression
--    so that we can reserve output variables for the expressions within
lengthOfExpr :: T.Expr -> Int
lengthOfExpr expr = case expr of
  T.Array xs -> length xs
  (T.Val T.Unit) -> 0
  _ -> 1

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
    -- | Number of input variables (they are placed before all variables)
    erasedNumOfInputVars :: !Int,
    -- | Number of output variables (they are placed after input variables)
    erasedOutputVarSize :: !Int,
    -- | Variables that are boolean (so that we can impose the Boolean constraint on them)
    erasedBoolVars :: !IntSet
  }

instance (GaloisField n, Integral n) => Show (TypeErased n) where
  show (TypeErased expr assertions assignments allVarsSize inputVarSize outputVarSize boolVars) =
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
      <> "  number of all variables: "
      <> show allVarsSize
      <> "\n  number of input variables: "
      <> show inputVarSize
      <> "\n  number of output variables: "
      <> show outputVarSize
      <> "\n  Boolean variables: "
      <> show (IntSet.toList boolVars)
      <> "\n\
         \}"

--------------------------------------------------------------------------------

-- monad for collecting boolean vars along the way
type M n = ReaderT (Int, Int) (State (Context n))

runM :: Int -> Int -> Int -> M n a -> (a, Context n)
runM inputVarSize outputVarSize nextVar =
  flip runState (initContext nextVar) . flip runReaderT (inputVarSize, outputVarSize)

-- | Context for type erasure
data Context n = Context
  { -- | Number of variables
    ctxNumOfVars :: !Int,
    -- | Set of Boolean variables (so that we can impose constraints like `$A * $A = $A` on them)
    ctxBoolVars :: !IntSet,
    -- | Assignments ($A = ...)
    ctxAssigments :: [Assignment n]
  }
  deriving (Show)

-- | Initial Context for type erasure
initContext :: Int -> Context n
initContext nextVar = Context nextVar IntSet.empty []

-- | Mark a variable as Boolean
-- so that we can later impose constraints on them (e.g. $A * $A = $A)
markAsBoolVar :: Var -> M n ()
markAsBoolVar var = modify' (\ctx -> ctx {ctxBoolVars = IntSet.insert var (ctxBoolVars ctx)})

-- | Generate a fresh new variable
freshVar :: M n Var
freshVar = do
  numberOfVars <- gets ctxNumOfVars
  modify' (\ctx -> ctx {ctxNumOfVars = succ (ctxNumOfVars ctx)})
  return numberOfVars

-- | Make a new assignment
makeAssignment :: Var -> Expr n -> M n ()
makeAssignment var expr = modify' (\ctx -> ctx {ctxAssigments = Assignment var expr : ctxAssigments ctx})

-- | Wire an expression with some variable
--   If the expression is already a variable, then we just return it
wireAsVar :: Expr n -> M n Var
wireAsVar (Var var) = return var
wireAsVar others = do
  var <- freshVar
  makeAssignment var others
  return var

--------------------------------------------------------------------------------

eraseType :: GaloisField n => T.Elaborated -> TypeErased n
eraseType (T.Elaborated expr comp) =
  let outputVarSize = lengthOfExpr expr
      T.Computation nextVar inputVarSize _nextAddr _heap numAsgns boolAsgns assertions = comp
      ((erasedExpr', erasedAssignments', erasedAssertions'), context) =
        runM inputVarSize outputVarSize nextVar $ do
          expr' <- eraseExpr expr
          numAssignments' <- mapM eraseAssignment numAsgns
          boolAssignments' <- mapM eraseAssignment boolAsgns
          let assignments = numAssignments' <> boolAssignments'
          assertions' <- concat <$> mapM eraseExpr assertions
          return (expr', assignments, assertions')
      Context nextVar' boolVars extraAssignments = context
   in TypeErased
        { erasedExpr = erasedExpr',
          erasedAssertions = erasedAssertions',
          erasedAssignments = erasedAssignments' <> extraAssignments,
          erasedNumOfVars = inputVarSize + outputVarSize + nextVar',
          erasedNumOfInputVars = inputVarSize,
          erasedOutputVarSize = outputVarSize,
          erasedBoolVars = boolVars
        }

eraseVal :: GaloisField n => T.Val -> M n [Expr n]
eraseVal (T.Integer n) = return [Val (fromInteger n)]
eraseVal (T.Rational n) = return [Val (fromRational n)]
eraseVal (T.Boolean False) = return [Val 0]
eraseVal (T.Boolean True) = return [Val 1]
eraseVal T.Unit = return []

eraseRef' :: T.Ref -> M n Int
eraseRef' ref = case ref of
  T.NumVar n -> relocateOrdinaryVar n
  T.NumInputVar n -> return n
  -- we don't need to mark intermediate Boolean variables
  -- and impose the Boolean constraint on them ($A * $A = $A)
  -- because this property should be guaranteed by the source of its value
  T.BoolVar n -> relocateOrdinaryVar n
  T.BoolInputVar n -> do
    markAsBoolVar n
    return n
  where
    -- we need to relocate ordinary variables
    -- so that we can place input variables and output variables in front of them
    relocateOrdinaryVar :: Int -> M n Int
    relocateOrdinaryVar n = do
      (inputVarSize, outputVarSize) <- ask
      return (inputVarSize + outputVarSize + n)

eraseRef :: GaloisField n => T.Ref -> M n (Expr n)
eraseRef ref = Var <$> eraseRef' ref

eraseExpr :: GaloisField n => T.Expr -> M n [Expr n]
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
  T.ToBool x -> do
    -- we need to wire the erased expression as variable and mark it as Boolean
    -- because there's no guarantee that the erased expression
    -- would behave like a Boolean (i.e. $A * $A = $A)
    vars <- eraseExpr x >>= mapM wireAsVar
    mapM_ markAsBoolVar vars
    return $ map Var vars
  T.ToNum x -> eraseExpr x

eraseAssignment :: GaloisField n => T.Assignment -> M n (Assignment n)
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

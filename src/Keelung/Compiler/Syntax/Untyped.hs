{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}

module Keelung.Compiler.Syntax.Untyped
  ( Op (..),
    BinaryOp (..),
    Expr (..),
    TypeErased (..),
    Assignment (..),
    eraseType,
    sizeOfExpr,
    bitValue,
  )
where

import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Proxy (asProxyTypeOf)
import Data.Sequence (Seq (..), (|>))
import Keelung.Compiler.Syntax.Bits (Bits (..))
import Keelung.Field (N (..))
import qualified Keelung.Syntax.Typed as T
import Keelung.Syntax.VarCounters
import Keelung.Types ( Var )

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
  | VarBit Var Int -- Bit of a variable
  -- Binary operators with only 2 operands
  | BinaryOp BinaryOp (Expr n) (Expr n)
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
          VarBit var i -> showString "$" . shows var . showString "[" . shows i . showString "]"
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
  VarBit _ _ -> 1
  NAryOp _ x0 x1 xs ->
    let operands = x0 :<| x1 :<| xs
     in sum (fmap sizeOfExpr operands) + (length operands - 1)
  BinaryOp _ x0 x1 -> sizeOfExpr x0 + sizeOfExpr x1 + 1
  If x y z -> 1 + sizeOfExpr x + sizeOfExpr y + sizeOfExpr z

-- | Calculate the "length" of an expression
--    so that we can reserve output variables for the expressions within
lengthOfExpr :: T.Expr -> Int
lengthOfExpr expr = case expr of
  T.Array xs -> sum $ fmap lengthOfExpr xs
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
    -- | Variable bookkeepung
    erasedVarCounters :: !VarCounters,
    -- | Assertions after type erasure
    erasedAssertions :: ![Expr n],
    -- | Assignments after type erasure
    erasedAssignments :: ![Assignment n],
    -- | Variables that are boolean (so that we can impose the Boolean constraint on them)
    erasedBoolVars :: !IntSet
  }

instance (GaloisField n, Integral n) => Show (TypeErased n) where
  show (TypeErased expr counters assertions assignments boolVars) =
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
      <> "  Boolean variables: "
      <> show (IntSet.toList boolVars)
      <> "\n\
         \}"

--------------------------------------------------------------------------------

-- monad for collecting boolean vars along the way
type M n = State (Context n)

runM :: VarCounters -> M n a -> a
runM counters = flip evalState (initContext counters)

-- | Context for type erasure
data Context n = Context
  { -- | Variable bookkeeping
    ctxVarCounters :: VarCounters,
    -- | Set of Boolean variables (so that we can impose constraints like `$A * $A = $A` on them)
    ctxBoolVars :: !IntSet,
    -- | Assignments ($A = ...)
    ctxAssigments :: [Assignment n]
  }
  deriving (Show)

-- | Initial Context for type erasure
initContext :: VarCounters -> Context n
initContext counters = Context counters IntSet.empty []

-- | Mark a variable as Boolean
-- so that we can later impose constraints on them (e.g. $A * $A = $A)
markAsBoolVar :: Var -> M n ()
markAsBoolVar var = modify' (\ctx -> ctx {ctxBoolVars = IntSet.insert var (ctxBoolVars ctx)})

-- | Generate a fresh new variable
freshVar :: M n Var
freshVar = do
  n <- gets (totalVarSize . ctxVarCounters)
  modify' (\ctx -> ctx {ctxVarCounters = bumpOrdinaryVar (ctxVarCounters ctx)})
  return n

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

eraseType :: (GaloisField n, Integral n) => T.Elaborated -> TypeErased n
eraseType (T.Elaborated expr comp) =
  let T.Computation counters numAsgns boolAsgns assertions = comp
   in runM counters $ do
        expr' <- eraseExpr expr
        numAssignments' <- mapM eraseAssignment numAsgns
        boolAssignments' <- mapM eraseAssignment boolAsgns
        let assignments = numAssignments' <> boolAssignments'
        assertions' <- concat <$> mapM eraseExpr assertions
        context <- get
        let Context counters' boolVars extraAssignments = context
        return $
          TypeErased
            { erasedExpr = expr',
              -- determine the size of output vars by looking at the length of the expression
              erasedVarCounters = setNumWidth (getNumWidth context) $ setOutputVarSize (lengthOfExpr expr) counters',
              erasedAssertions = assertions',
              erasedAssignments = assignments <> extraAssignments,
              erasedBoolVars = boolVars
            }
  where
    getNumWidth :: Bits n => Context n -> Int
    getNumWidth proxy = bitSize $ asProxyTypeOf 0 proxy

eraseVal :: GaloisField n => T.Val -> M n [Expr n]
eraseVal (T.Integer n) = return [Val (fromInteger n)]
eraseVal (T.Rational n) = return [Val (fromRational n)]
eraseVal (T.Boolean False) = return [Val 0]
eraseVal (T.Boolean True) = return [Val 1]
eraseVal T.Unit = return []

eraseRef' :: T.Ref -> M n Int
eraseRef' ref = case ref of
  T.NumVar n -> relocateOrdinaryVar n
  T.NumInputVar n -> relocateNumInputVar n
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
      offset <- gets (pinnedVarSize . ctxVarCounters)
      return (offset + n)

    relocateNumInputVar :: Int -> M n Int
    relocateNumInputVar n = do
      offset <- gets (boolInputVarSize . ctxVarCounters)
      return (offset + n)

eraseRef :: GaloisField n => T.Ref -> M n (Expr n)
eraseRef ref = Var <$> eraseRef' ref

eraseExpr :: (GaloisField n, Integral n) => T.Expr -> M n [Expr n]
eraseExpr expr = case expr of
  T.Val val -> eraseVal val
  T.Var ref -> pure <$> eraseRef ref
  T.Array exprs -> do
    exprss <- mapM eraseExpr exprs
    return $ concat exprss
  T.Add x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprsOfAssocOp Add (head xs) (head ys)]
  T.Sub x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [BinaryOp Sub (head xs) (head ys)]
  T.Mul x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprsOfAssocOp Mul (head xs) (head ys)]
  T.Div x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [BinaryOp Div (head xs) (head ys)]
  T.Eq x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprsOfAssocOp Eq (head xs) (head ys)]
  T.And x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprsOfAssocOp And (head xs) (head ys)]
  T.Or x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprsOfAssocOp Or (head xs) (head ys)]
  T.Xor x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprsOfAssocOp Xor (head xs) (head ys)]
  T.BEq x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprsOfAssocOp BEq (head xs) (head ys)]
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
  T.Bit x i -> do
    x' <- head <$> eraseExpr x
    return [bitValue x' i]

bitValue :: (Integral n, GaloisField n) => Expr n -> Int -> Expr n
bitValue expr i = case expr of
  Val n -> Val (testBit n i)
  Var v -> VarBit v i
  VarBit {} -> error "Panic: trying to access the bit value of another bit value"
  BinaryOp {} -> error "Panic: trying to access the bit value of a compound expression"
  NAryOp {} -> error "Panic: trying to access the bit value of a compound expression"
  If p a b -> If p (bitValue a i) (bitValue b i)

eraseAssignment :: (GaloisField n, Integral n) => T.Assignment -> M n (Assignment n)
eraseAssignment (T.Assignment ref expr) = do
  var <- eraseRef' ref
  exprs <- eraseExpr expr
  return $ Assignment var (head exprs)

-- Flatten and chain expressions with associative operator together when possible
chainExprsOfAssocOp :: Op -> Expr n -> Expr n -> Expr n
chainExprsOfAssocOp op x y = case (x, y) of
  (NAryOp op1 x0 x1 xs, NAryOp op2 y0 y1 ys)
    | op1 == op2 && op2 == op ->
      -- chaining `op`, `op1`, and `op2`
      NAryOp op x0 x1 (xs <> (y0 :<| y1 :<| ys))
  (NAryOp op1 x0 x1 xs, _)
    | op1 == op ->
      -- chaining `op` and `op1`
      NAryOp op x0 x1 (xs |> y)
  (_, NAryOp op2 y0 y1 ys)
    | op2 == op ->
      -- chaining `op` and `op2`
      NAryOp op x y0 (y1 :<| ys)
  -- there's nothing left we can do
  _ -> NAryOp op x y mempty

-------------------------------------------------------------------------------

-- instance KnownNat n => Bits (Binary n) where
--   x .&. y = fromInteger (toInteger x .&. toInteger y)
--   x .|. y = fromInteger (toInteger x .|. toInteger y)
--   xor x y = fromInteger (toInteger x `xor` toInteger y)
--   complement = fromInteger . complement . toInteger
--   shift x i = fromInteger (shift (toInteger x) i)
--   rotate x i = fromInteger (rotate (toInteger x) i)
--   bitSize x = fromIntegral $ natVal x
--   bitSizeMaybe x = Just $ fromIntegral $ natVal x
--   isSigned _ = False
--   testBit x i = _
--   bit = _
--   popCount = _

-- bitValueGF181 :: Expr n -> Int -> M n n
-- bitValueGF181 expr i = case expr of

module Keelung.Compiler.Syntax.Erase (run) where

import Control.Monad.State
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Maybe (fromMaybe)
import Data.Proxy (asProxyTypeOf)
import Data.Sequence (Seq (..), (|>))
import Keelung.Compiler.Syntax.Bits (Bits (..))
import Keelung.Compiler.Syntax.Untyped
import qualified Keelung.Syntax.Typed as T
import Keelung.Syntax.VarCounters
import Keelung.Types (Var)

run :: (GaloisField n, Integral n) => T.Elaborated -> TypeErased n
run (T.Elaborated expr comp) =
  let T.Computation counters numAsgns boolAsgns assertions = comp
   in runM counters $ do
        -- update VarCounters.varNumWidth before type erasure
        context <- get
        let counters' = setNumWidth (deviseNumWidth context) $ setOutputVarSize (lengthOfExpr expr) counters
        let context' = context {ctxVarCounters = counters'}
        put context'
        -- start type erasure
        expr' <- eraseExpr expr
        numAssignments' <- mapM eraseAssignment numAsgns
        boolAssignments' <- mapM eraseAssignment boolAsgns
        let assignments = numAssignments' <> boolAssignments'
        assertions' <- concat <$> mapM eraseExpr assertions

        -- for the moment, each Number input variable
        -- incurs N additional Boolean input variables
        -- where N is the bit-length of the field
        let boolVarsFromNumInputs =
              IntSet.fromList
                [ boolInputVarSize counters' + numInputVarSize counters'
                  .. inputVarSize counters' - 1
                ]

        -- retrieve updated Context and return it
        Context counters'' boolVars <- get

        let numWidth = getNumWidth counters''
        let binReps =
              IntMap.fromList $
                map
                  ( \v ->
                      (v, (fromMaybe (error "cannot get bit var") (getBitVar counters'' v 0), numWidth))
                  )
                  (numInputVars counters'')

        return $
          TypeErased
            { erasedExpr = expr',
              -- determine the size of output vars by looking at the length of the expression
              erasedVarCounters = counters'',
              erasedAssertions = assertions',
              erasedAssignments = assignments,
              erasedBoolVars = boolVars <> boolVarsFromNumInputs,
              erasedBinReps = binReps
            }
  where
    deviseNumWidth :: (GaloisField n, Integral n) => Context n -> Int
    deviseNumWidth proxy = bitSize $ asProxyTypeOf 0 proxy
    lengthOfExpr :: T.Expr -> Int
    lengthOfExpr (T.Array xs) = sum $ fmap lengthOfExpr xs
    lengthOfExpr (T.Val T.Unit) = 0
    lengthOfExpr _ = 1

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
    ctxBoolVars :: !IntSet
  }
  deriving (Show)

-- | Initial Context for type erasure
initContext :: VarCounters -> Context n
initContext counters = Context counters mempty

-- | Mark a variable as Boolean
-- so that we can later impose constraints on them (e.g. $A * $A = $A)
markAsBoolVar :: Var -> M n ()
markAsBoolVar var = modify' (\ctx -> ctx {ctxBoolVars = IntSet.insert var (ctxBoolVars ctx)})

--------------------------------------------------------------------------------

eraseVal :: GaloisField n => T.Val -> M n [Expr n]
eraseVal (T.Integer n) = return [Val (fromInteger n)]
eraseVal (T.Rational n) = return [Val (fromRational n)]
eraseVal (T.Boolean False) = return [Val 0]
eraseVal (T.Boolean True) = return [Val 1]
eraseVal T.Unit = return []

eraseRef' :: T.Ref -> M n Int
eraseRef' ref = case ref of
  T.NumVar n -> relocateIntermediateVar n
  T.NumInputVar n -> return n
  -- we don't need to mark intermediate Boolean variables
  -- and impose the Boolean constraint on them ($A * $A = $A)
  -- because this property should be guaranteed by the source of its value
  T.BoolVar n -> relocateIntermediateVar n
  T.BoolInputVar n -> do
    markAsBoolVar n
    return n
  where
    -- we need to relocate ordinary variables
    -- so that we can place input variables and output variables in front of them
    relocateIntermediateVar :: Int -> M n Int
    relocateIntermediateVar n = do
      offset <- gets (pinnedVarSize . ctxVarCounters)
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
  T.ToNum x -> eraseExpr x
  T.Bit x i -> do
    x' <- head <$> eraseExpr x
    value <- bitValue x' i
    return [value]

bitValue :: (Integral n, GaloisField n) => Expr n -> Int -> M n (Expr n)
bitValue expr i = case expr of
  Val n -> return $ Val (testBit n i)
  Var var -> do
    counters <- gets ctxVarCounters
    -- if the index 'i' overflows or underflows, wrap it around
    let numWidth = getNumWidth counters
    let i' = i `mod` numWidth
    -- bit variable corresponding to the variable 'var' and the index 'i''
    case getBitVar counters var i' of
      Nothing -> error $ "Panic: unable to get perform bit test on $" <> show var <> "[" <> show i' <> "]"
      Just bitVar -> return $ Var bitVar
  BinaryOp {} -> error "Panic: trying to access the bit value of a compound expression"
  NAryOp {} -> error "Panic: trying to access the bit value of a compound expression"
  If p a b -> If p <$> bitValue a i <*> bitValue b i

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

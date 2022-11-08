module Keelung.Compiler.Syntax.Erase (run) where

import Control.Monad.State
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..), (|>))
import Keelung.Compiler.Syntax.Bits (Bits (..))
import Keelung.Compiler.Syntax.Untyped
import qualified Keelung.Syntax.Typed as T
import Keelung.Syntax.VarCounters

run :: (GaloisField n, Integral n) => T.Elaborated -> TypeErased n
run (T.Elaborated expr comp) =
  let T.Computation counters numAsgns boolAsgns _ assertions = comp
      proxy = 0
   in runM counters $ do
        -- update VarCounters.varNumWidth before type erasure
        let counters' = setNumBitWidth (bitSize proxy) $ setOutputVarSize (lengthOfExpr expr) counters
        put counters'
        -- start type erasure
        expr' <- eraseExpr expr
        sameType proxy expr'
        numAssignments' <- mapM eraseAssignment numAsgns
        boolAssignments' <- mapM eraseAssignment boolAsgns
        let assignments = numAssignments' <> boolAssignments'
        assertions' <- concat <$> mapM eraseExpr assertions

        -- retrieve updated Context and return it
        counters'' <- get

        -- associate input variables with their corresponding binary representation
        let numBinReps =
              let (start, end) = numInputVarsRange counters''
               in IntMap.fromList $
                    map
                      ( \v ->
                          (v, fromMaybe (error ("Panic: cannot query bits of var $" <> show v)) (lookupBinRepStart counters'' v))
                      )
                      [start .. end - 1]

        let customBinReps =
              fmap
                ( \(start, end) ->
                    IntMap.fromList $
                      map
                        ( \var ->
                            (var, fromMaybe (error ("Panic: cannot query bits of var $" <> show var)) (lookupBinRepStart counters'' var))
                        )
                        [start .. end - 1]
                )
                (customInputVarsRanges counters'')

        return $
          TypeErased
            { erasedExpr = expr',
              -- determine the size of output vars by looking at the length of the expression
              erasedVarCounters = counters'',
              erasedAssertions = assertions',
              erasedAssignments = assignments,
              erasedBinReps = numBinReps,
              erasedCustomBinReps = customBinReps
            }
  where
    -- proxy trick for devising the bit width of field elements
    sameType :: n -> [Expr n] -> M n ()
    sameType _ _ = return ()

    lengthOfExpr :: T.Expr -> Int
    lengthOfExpr (T.Array xs) = sum $ fmap lengthOfExpr xs
    lengthOfExpr (T.Val T.Unit) = 0
    lengthOfExpr _ = 1

--------------------------------------------------------------------------------

-- monad for collecting boolean vars along the way
type M n = State VarCounters

runM :: VarCounters -> M n a -> a
runM = flip evalState

--------------------------------------------------------------------------------

eraseVal :: GaloisField n => T.Val -> M n [Expr n]
eraseVal (T.Integer n) = return [Val Number (fromInteger n)]
eraseVal (T.Rational n) = return [Val Number (fromRational n)]
eraseVal (T.Unsigned w n) = return [Val (UInt w) (fromInteger n)]
eraseVal (T.Boolean False) = return [Val Boolean 0]
eraseVal (T.Boolean True) = return [Val Boolean 1]
eraseVal T.Unit = return []

-- Current layout of variables
--
-- ┏━━━━━━━━━━━━━━━━━┓
-- ┃         Output  ┃
-- ┣─────────────────┫
-- ┃   Number Input  ┃
-- ┣─────────────────┫
-- ┃   Custom Input  ┃
-- ┣─────────────────┫─ ─ ─ ─ ─ ─ ─ ─
-- ┃  Boolean Input  ┃               │
-- ┣─────────────────┫
-- ┃  Binary Rep of  ┃
-- ┃   Number Input  ┃   Contiguous chunk of bits
-- ┣─────────────────┫
-- ┃  Binary Rep of  ┃
-- ┃   Custom Input  ┃               │
-- ┣─────────────────┫─ ─ ─ ─ ─ ─ ─ ─
-- ┃   Intermediate  ┃
-- ┗━━━━━━━━━━━━━━━━━┛
--
eraseRef' :: T.Ref -> M n (BitWidth, Int)
eraseRef' ref = do
  counters <- get
  return $ case ref of
    T.NumVar n -> (Number, blendIntermediateVar counters n)
    T.NumInputVar n -> (Number, blendNumInputVar counters n)
    -- we don't need to mark intermediate Boolean variables
    -- and impose the Boolean constraint on them ($A * $A = $A)
    -- because this property should be guaranteed by the source of its value
    T.BoolVar n -> (Boolean, blendIntermediateVar counters n)
    T.BoolInputVar n -> (Boolean, blendBoolInputVar counters n)
    T.UIntVar w n -> (UInt w, blendIntermediateVar counters n)
    T.UIntInputVar w n -> (UInt w, blendCustomInputVar counters n)

eraseRef :: GaloisField n => T.Ref -> M n (Expr n)
eraseRef ref = uncurry Var <$> eraseRef' ref

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
    return [BinaryOp (bitWidthOf (head xs)) Sub (head xs) (head ys)]
  T.Mul x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [chainExprsOfAssocOp Mul (head xs) (head ys)]
  T.Div x y -> do
    xs <- eraseExpr x
    ys <- eraseExpr y
    return [BinaryOp (bitWidthOf (head xs)) Div (head xs) (head ys)]
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
    return [If (bitWidthOf (head xs)) (head bs) (head xs) (head ys)]
  T.ToNum x -> eraseExpr x
  T.Bit x i -> do
    x' <- head <$> eraseExpr x
    value <- bitValue x' i
    return [value]

bitValue :: (Integral n, GaloisField n) => Expr n -> Int -> M n (Expr n)
bitValue expr i = case expr of
  Val w n -> return $ Val w (testBit n i)
  Var w var -> do
    counters <- get
    -- if the index 'i' overflows or underflows, wrap it around

    let i' = case w of
          Boolean -> 0
          Number -> i `mod` getNumBitWidth counters
          UInt n -> i `mod` n
    -- bit variable corresponding to the variable 'var' and the index 'i''
    case lookupBinRepStart counters var of
      Nothing -> error $ "Panic: unable to get perform bit test on $" <> show var <> "[" <> show i' <> "]"
      Just start -> return $ Var Boolean (start + i')
  BinaryOp {} -> error "Panic: trying to access the bit value of a compound expression"
  NAryOp {} -> error "Panic: trying to access the bit value of a compound expression"
  If w p a b -> If w p <$> bitValue a i <*> bitValue b i

eraseAssignment :: (GaloisField n, Integral n) => T.Assignment -> M n (Assignment n)
eraseAssignment (T.Assignment ref expr) = do
  (_, var) <- eraseRef' ref
  exprs <- eraseExpr expr
  return $ Assignment var (head exprs)

-- Flatten and chain expressions with associative operator together when possible
chainExprsOfAssocOp :: Op -> Expr n -> Expr n -> Expr n
chainExprsOfAssocOp op x y = case (x, y) of
  (NAryOp w op1 x0 x1 xs, NAryOp _ op2 y0 y1 ys)
    | op1 == op2 && op2 == op ->
      -- chaining `op`, `op1`, and `op2`
      NAryOp w op x0 x1 (xs <> (y0 :<| y1 :<| ys))
  (NAryOp w op1 x0 x1 xs, _)
    | op1 == op ->
      -- chaining `op` and `op1`
      NAryOp w op x0 x1 (xs |> y)
  (_, NAryOp w op2 y0 y1 ys)
    | op2 == op ->
      -- chaining `op` and `op2`
      NAryOp w op x y0 (y1 :<| ys)
  -- there's nothing left we can do
  _ -> NAryOp (bitWidthOf x) op x y mempty

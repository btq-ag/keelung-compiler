module Keelung.Compiler.Syntax.Erase (run) where

import Control.Monad.State
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..), (|>))
import Keelung.Compiler.Syntax.FieldBits (FieldBits (..))
import Keelung.Compiler.Syntax.Untyped
import qualified Keelung.Syntax.BinRep as BinRep
import qualified Keelung.Syntax.Typed as T
import Keelung.Syntax.VarCounters

run :: (GaloisField n, Integral n) => T.Elaborated -> TypeErased n
run (T.Elaborated expr comp) =
  let T.Computation counters numAsgns boolAsgns _ assertions = comp
      proxy = 0
   in runM counters $ do
        -- update VarCounters.varNumWidth before type erasure
        let numBitWidth = bitSize proxy
        let counters' = setNumBitWidth numBitWidth $ setOutputVarSize (lengthOfExpr expr) counters
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
               in BinRep.fromList $
                    map
                      (\v -> BinRep.fromNumBinRep numBitWidth (v, fromMaybe (error ("Panic: cannot query bits of var $" <> show v)) (lookupBinRepStart counters'' v)))
                      [start .. end - 1]

        let customBinReps =
              BinRep.fromList $
                concatMap
                  ( \(width, (start, end)) ->
                      map
                        (\v -> BinRep.fromNumBinRep width (v, fromMaybe (error ("Panic: cannot query bits of var $" <> show v)) (lookupBinRepStart counters'' v)))
                        [start .. end - 1]
                  )
                  (IntMap.toList (customInputVarsRanges counters''))

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
eraseVal (T.Integer n) = do
  width <- gets getNumBitWidth
  return [Val (Number width) (fromInteger n)]
eraseVal (T.Rational n) = do
  width <- gets getNumBitWidth
  return [Val (Number width) (fromRational n)]
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
  let numWidth = getNumBitWidth counters
  return $ case ref of
    T.NumVar n -> (Number numWidth, blendIntermediateVar counters n)
    T.NumInputVar n -> (Number numWidth, blendNumInputVar counters n)
    -- we don't need to mark intermediate Boolean variables
    -- and impose the Boolean constraint on them ($A * $A = $A)
    -- because this property should be guaranteed by the source of its value
    T.BoolVar n -> (Boolean, blendIntermediateVar counters n)
    T.BoolInputVar n -> (Boolean, blendBoolInputVar counters n)
    T.UIntVar w n -> (UInt w, blendIntermediateVar counters n)
    T.UIntInputVar w n -> (UInt w, blendCustomInputVar counters w n)

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
  T.RotateR n x -> do
    xs <- eraseExpr x
    return [Rotate (bitWidthOf (head xs)) n (head xs)]
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
    let i' = i `mod` getWidth w
    -- bit variable corresponding to the variable 'var' and the index 'i''
    case lookupBinRepStart counters var of
      Nothing -> error $ "Panic: unable to get perform bit test on $" <> show var <> "[" <> show i' <> "]"
      Just start -> return $ Var Boolean (start + i')
  Rotate w n x -> do
    -- rotate the bit value
    -- if the index 'i' overflows or underflows, wrap it around
    let i' = n + i `mod` getWidth w
    bitValue x i'
  BinaryOp {} -> error "Panic: trying to access the bit value of a compound expression"
  NAryOp _ And x y rest ->
    NAryOp Boolean And
      <$> bitValue x i
      <*> bitValue y i
      <*> mapM (`bitValue` i) rest
  NAryOp _ Or x y rest ->
    NAryOp Boolean Or
      <$> bitValue x i
      <*> bitValue y i
      <*> mapM (`bitValue` i) rest
  NAryOp _ Xor x y rest ->
    NAryOp Boolean Xor
      <$> bitValue x i
      <*> bitValue y i
      <*> mapM (`bitValue` i) rest
  NAryOp {} -> error "Panic: trying to access the bit value of a compound expression"
  If w p a b -> If w p <$> bitValue a i <*> bitValue b i
  EmbedR1C {} -> error "Panic: trying to access the bit value of a R1C"

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

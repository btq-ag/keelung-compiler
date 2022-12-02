module Keelung.Compiler.Syntax.Erase (run) where

import Control.Monad.Reader
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap.Strict as IntMap
import Data.Sequence (Seq (..), (|>))
import Keelung.Compiler.Constraint2
import Keelung.Compiler.Syntax.FieldBits (FieldBits (..))
import Keelung.Compiler.Syntax.Untyped
import qualified Keelung.Syntax.Typed as T

run :: (GaloisField n, Integral n) => T.Elaborated -> TypeErased n
run (T.Elaborated expr comp) =
  let T.Computation counters aF aFI bF bFI _ _ assertions = comp
      proxy = 0
      numBitWidth = bitSize proxy
   in runM numBitWidth $ do
        -- start type erasure
        expr' <- eraseExpr expr
        sameType proxy expr'
        assignmentsF <- mapM (\(var, val) -> AssignmentF (RefF var) <$> eraseExprN val) (IntMap.toList aF)
        assignmentsFI <- mapM (\(var, val) -> AssignmentF (RefFI var) <$> eraseExprN val) (IntMap.toList aFI)
        assignmentsB <- mapM (\(var, val) -> AssignmentB (RefB var) <$> eraseExprB val) (IntMap.toList bF)
        assignmentsBI <- mapM (\(var, val) -> AssignmentB (RefBI var) <$> eraseExprB val) (IntMap.toList bFI)
        let assignments = assignmentsF ++ assignmentsFI ++ assignmentsB ++ assignmentsBI
        assertions' <- concat <$> mapM eraseExpr assertions

        return $
          TypeErased
            { erasedExpr = expr',
              erasedFieldBitWidth = numBitWidth,
              -- determine the size of output vars by looking at the length of the expression
              erasedCounters = counters,
              erasedRelations = mempty,
              erasedAssertions = assertions',
              erasedAssignments = assignments,
              erasedBinReps = mempty,
              erasedCustomBinReps = mempty
            }
  where
    -- proxy trick for devising the bit width of field elements
    sameType :: n -> [Expr n] -> M n ()
    sameType _ _ = return ()

--------------------------------------------------------------------------------

-- monad for collecting boolean vars along the way
type M n = Reader Width

runM :: Width -> M n a -> a
runM width f = runReader f width

--------------------------------------------------------------------------------

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
eraseExprB :: (GaloisField n, Integral n) => T.Boolean -> M n (ExprB n)
eraseExprB expr = case expr of
  T.ValB True -> return $ ValB 1
  T.ValB False -> return $ ValB 0
  T.VarB var -> return $ VarB var
  T.InputVarB var -> return $ InputVarB var
  T.AndB x y -> chainExprsOfAssocOpAndB <$> eraseExprB x <*> eraseExprB y
  T.OrB x y -> chainExprsOfAssocOpOrB <$> eraseExprB x <*> eraseExprB y
  T.XorB x y -> XorB <$> eraseExprB x <*> eraseExprB y
  T.NotB x -> NotB <$> eraseExprB x
  T.IfB p x y -> IfB <$> eraseExprB p <*> eraseExprB x <*> eraseExprB y
  T.EqB x y -> EqB <$> eraseExprB x <*> eraseExprB y
  T.EqN x y -> EqN <$> eraseExprN x <*> eraseExprN y
  T.EqU _ x y -> EqU <$> eraseExprU x <*> eraseExprU y
  T.BitU _ x i -> BitU <$> eraseExprU x <*> pure i

eraseExprN :: (GaloisField n, Integral n) => T.Number -> M n (ExprN n)
eraseExprN expr = do
  w <- ask
  case expr of
    T.ValN x -> return $ ValN w (fromInteger x)
    T.ValNR x -> return $ ValN w (fromRational x)
    T.VarN var -> return $ VarN w var
    T.InputVarN var -> return $ InputVarN w var
    T.AddN x y -> chainExprsOfAssocOpAddN w <$> eraseExprN x <*> eraseExprN y
    T.SubN x y -> SubN w <$> eraseExprN x <*> eraseExprN y
    T.MulN x y -> MulN w <$> eraseExprN x <*> eraseExprN y
    T.DivN x y -> DivN w <$> eraseExprN x <*> eraseExprN y
    T.IfN p x y -> IfN w <$> eraseExprB p <*> eraseExprN x <*> eraseExprN y
    T.BtoN x -> BtoN w <$> eraseExprB x

eraseExprU :: (GaloisField n, Integral n) => T.UInt -> M n (ExprU n)
eraseExprU expr = case expr of
  T.ValU w n -> return $ ValU w (fromIntegral n)
  T.VarU w var -> return $ VarU w var
  T.InputVarU w var -> return $ InputVarU w var
  T.AddU w x y -> AddU w <$> eraseExprU x <*> eraseExprU y
  T.SubU w x y -> SubU w <$> eraseExprU x <*> eraseExprU y
  T.MulU w x y -> MulU w <$> eraseExprU x <*> eraseExprU y
  T.AndU w x y -> chainExprsOfAssocOpAndU w <$> eraseExprU x <*> eraseExprU y
  T.OrU w x y -> chainExprsOfAssocOpOrU w <$> eraseExprU x <*> eraseExprU y
  T.XorU w x y -> XorU w <$> eraseExprU x <*> eraseExprU y
  T.NotU w x -> NotU w <$> eraseExprU x
  T.RoLU w i x -> RoLU w i <$> eraseExprU x
  T.ShLU w i x -> ShLU w i <$> eraseExprU x
  T.IfU w p x y -> IfU w <$> eraseExprB p <*> eraseExprU x <*> eraseExprU y
  T.BtoU w x -> BtoU w <$> eraseExprB x

eraseExpr :: (GaloisField n, Integral n) => T.Expr -> M n [Expr n]
eraseExpr expr = case expr of
  T.Unit -> return []
  T.Boolean x -> do
    x' <- eraseExprB x
    return [ExprB x']
  T.Number x -> do
    x' <- eraseExprN x
    return [ExprN x']
  T.UInt x -> do
    x' <- eraseExprU x
    return [ExprU x']
  -- T.Var ref -> pure <$> eraseRef3 ref
  T.Array exprs -> do
    exprss <- mapM eraseExpr exprs
    return (concat exprss)

-- | Flatten and chain expressions with associative operator together when possible
chainExprsOfAssocOpAddN :: Width -> ExprN n -> ExprN n -> ExprN n
chainExprsOfAssocOpAddN w x y = case (x, y) of
  (AddN _ x0 x1 xs, AddN _ y0 y1 ys) ->
    AddN w x0 x1 (xs <> (y0 :<| y1 :<| ys))
  (AddN _ x0 x1 xs, _) ->
    AddN w x0 x1 (xs |> y)
  (_, AddN _ y0 y1 ys) ->
    AddN w x y0 (y1 :<| ys)
  -- there's nothing left we can do
  _ -> AddN w x y mempty

chainExprsOfAssocOpAndB :: ExprB n -> ExprB n -> ExprB n
chainExprsOfAssocOpAndB x y = case (x, y) of
  (AndB x0 x1 xs, AndB y0 y1 ys) ->
    AndB x0 x1 (xs <> (y0 :<| y1 :<| ys))
  (AndB x0 x1 xs, _) ->
    AndB x0 x1 (xs |> y)
  (_, AndB y0 y1 ys) ->
    AndB x y0 (y1 :<| ys)
  -- there's nothing left we can do
  _ -> AndB x y mempty

chainExprsOfAssocOpAndU :: Width -> ExprU n -> ExprU n -> ExprU n
chainExprsOfAssocOpAndU w x y = case (x, y) of
  (AndU _ x0 x1 xs, AndU _ y0 y1 ys) ->
    AndU w x0 x1 (xs <> (y0 :<| y1 :<| ys))
  (AndU _ x0 x1 xs, _) ->
    AndU w x0 x1 (xs |> y)
  (_, AndU _ y0 y1 ys) ->
    AndU w x y0 (y1 :<| ys)
  -- there's nothing left we can do
  _ -> AndU w x y mempty

chainExprsOfAssocOpOrB :: ExprB n -> ExprB n -> ExprB n
chainExprsOfAssocOpOrB x y = case (x, y) of
  (OrB x0 x1 xs, OrB y0 y1 ys) ->
    OrB x0 x1 (xs <> (y0 :<| y1 :<| ys))
  (OrB x0 x1 xs, _) ->
    OrB x0 x1 (xs |> y)
  (_, OrB y0 y1 ys) ->
    OrB x y0 (y1 :<| ys)
  -- there's nothing left we can do
  _ -> OrB x y mempty

chainExprsOfAssocOpOrU :: Width -> ExprU n -> ExprU n -> ExprU n
chainExprsOfAssocOpOrU w x y = case (x, y) of
  (OrU _ x0 x1 xs, OrU _ y0 y1 ys) ->
    OrU w x0 x1 (xs <> (y0 :<| y1 :<| ys))
  (OrU _ x0 x1 xs, _) ->
    OrU w x0 x1 (xs |> y)
  (_, OrU _ y0 y1 ys) ->
    OrU w x y0 (y1 :<| ys)
  -- there's nothing left we can do
  _ -> OrU w x y mempty
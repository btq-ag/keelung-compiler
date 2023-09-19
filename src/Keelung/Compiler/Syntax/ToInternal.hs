module Keelung.Compiler.Syntax.ToInternal (run) where

import Control.Monad.Reader
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.Sequence (Seq (..), (|>))
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.FieldInfo
import Keelung.Syntax (HasWidth (widthOf), Var)
import Keelung.Syntax.Counters
import Keelung.Syntax.Encode.Syntax qualified as T

run :: (GaloisField n, Integral n) => FieldInfo -> T.Elaborated -> Internal n
run fieldInfo (T.Elaborated expr comp) =
  let T.Computation counters assertions sideEffects = comp
      proxy = 0
   in runM counters (fieldWidth fieldInfo) $ do
        exprs <- sameType proxy <$> convertExprAndAllocOutputVar expr
        assertions' <- concat <$> mapM convertExpr assertions
        counters' <- get
        sideEffects' <- mapM convertSideEffect sideEffects
        return $
          Internal
            { internalExpr = exprs,
              internalFieldBitWidth = fieldWidth fieldInfo,
              internalCounters = counters',
              internalAssertions = assertions',
              internalSideEffects = sideEffects'
            }
  where
    -- proxy trick for devising the bit width of field elements
    sameType :: n -> [(Var, Expr n)] -> [(Var, Expr n)]
    sameType _ = id

--------------------------------------------------------------------------------

-- monad for collecting boolean vars along the way
type M n = StateT Counters (Reader Width)

runM :: Counters -> Width -> M n a -> a
runM counters width f = runReader (evalStateT f counters) width

--------------------------------------------------------------------------------

convertSideEffect :: (GaloisField n, Integral n) => T.SideEffect -> M n (SideEffect n)
convertSideEffect (T.AssignmentF var val) = AssignmentF var <$> convertExprF val
convertSideEffect (T.AssignmentB var val) = AssignmentB var <$> convertExprB val
convertSideEffect (T.AssignmentU width var val) = AssignmentU width var <$> convertExprU val
convertSideEffect (T.DivMod width dividend divisor quotient remainder) = DivMod width <$> convertExprU dividend <*> convertExprU divisor <*> convertExprU quotient <*> convertExprU remainder
convertSideEffect (T.AssertLTE width val bound) = AssertLTE width <$> convertExprU val <*> pure bound
convertSideEffect (T.AssertLT width val bound) = AssertLT width <$> convertExprU val <*> pure bound
convertSideEffect (T.AssertGTE width val bound) = AssertGTE width <$> convertExprU val <*> pure bound
convertSideEffect (T.AssertGT width val bound) = AssertGT width <$> convertExprU val <*> pure bound

--------------------------------------------------------------------------------

convertExprB :: (GaloisField n, Integral n) => T.Boolean -> M n (ExprB n)
convertExprB expr = case expr of
  T.ValB val -> return $ ValB val
  T.VarB var -> return $ VarB var
  T.VarBI var -> return $ VarBI var
  T.VarBP var -> return $ VarBP var
  T.AndB x y -> chainExprsOfAssocOpAndB <$> convertExprB x <*> convertExprB y
  T.OrB x y -> chainExprsOfAssocOpOrB <$> convertExprB x <*> convertExprB y
  T.XorB x y -> chainExprsOfAssocOpXorB <$> convertExprB x <*> convertExprB y
  T.NotB x -> NotB <$> convertExprB x
  T.IfB p x y -> IfB <$> convertExprB p <*> convertExprB x <*> convertExprB y
  T.EqB x y -> EqB <$> convertExprB x <*> convertExprB y
  T.EqF x y -> EqF <$> convertExprF x <*> convertExprF y
  T.EqU _ x y -> EqU <$> convertExprU x <*> convertExprU y
  T.LTU _ x y -> LTU <$> convertExprU x <*> convertExprU y
  T.LTEU _ x y -> LTEU <$> convertExprU x <*> convertExprU y
  T.GTU _ x y -> GTU <$> convertExprU x <*> convertExprU y
  T.GTEU _ x y -> GTEU <$> convertExprU x <*> convertExprU y
  T.BitU _ x i -> BitU <$> convertExprU x <*> pure i

convertExprF :: (GaloisField n, Integral n) => T.Field -> M n (ExprF n)
convertExprF expr = case expr of
  T.ValF x -> return $ ValF (fromInteger x)
  T.ValFR x -> return $ ValF (fromRational x)
  T.VarF var -> return $ VarF var
  T.VarFI var -> return $ VarFI var
  T.VarFP var -> return $ VarFP var
  T.AddF x y -> chainExprsOfAssocOpAddF <$> convertExprF x <*> convertExprF y
  T.SubF x y -> SubF <$> convertExprF x <*> convertExprF y
  T.MulF x y -> MulF <$> convertExprF x <*> convertExprF y
  T.ExpF x n -> ExpF <$> convertExprF x <*> pure n
  T.DivF x y -> DivF <$> convertExprF x <*> convertExprF y
  T.IfF p x y -> IfF <$> convertExprB p <*> convertExprF x <*> convertExprF y
  T.BtoF x -> BtoF <$> convertExprB x

convertExprU :: (GaloisField n, Integral n) => T.UInt -> M n (ExprU n)
convertExprU expr = case expr of
  T.ValU w n -> return $ ValU w (fromIntegral n)
  T.VarU w var -> return $ VarU w var
  T.VarUI w var -> return $ VarUI w var
  T.VarUP w var -> return $ VarUP w var
  T.AddU w x y -> chainExprsOfAssocOpAddU w <$> convertExprU x <*> pure True <*> convertExprU y <*> pure True
  T.SubU w x y -> chainExprsOfAssocOpAddU w <$> convertExprU x <*> pure True <*> convertExprU y <*> pure False
  T.MulU w x y -> MulU w <$> convertExprU x <*> convertExprU y
  T.CLMulU w x y -> CLMulU w <$> convertExprU x <*> convertExprU y
  T.MMIU w x p -> MMIU w <$> convertExprU x <*> pure p
  T.AndU w x y -> chainExprsOfAssocOpAndU w <$> convertExprU x <*> convertExprU y
  T.OrU w x y -> chainExprsOfAssocOpOrU w <$> convertExprU x <*> convertExprU y
  T.XorU w x y -> chainExprsOfAssocOpXorU w <$> convertExprU x <*> convertExprU y
  T.NotU w x -> NotU w <$> convertExprU x
  T.RoLU w i x -> RoLU w i <$> convertExprU x
  T.ShLU w i x -> ShLU w i <$> convertExprU x
  T.SetU w x i b -> SetU w <$> convertExprU x <*> pure i <*> convertExprB b
  T.IfU w p x y -> IfU w <$> convertExprB p <*> convertExprU x <*> convertExprU y
  T.BtoU w x -> BtoU w <$> convertExprB x

convertExprAndAllocOutputVar :: (GaloisField n, Integral n) => T.Expr -> M n [(Var, Expr n)]
convertExprAndAllocOutputVar expr = case expr of
  T.Unit -> return []
  T.Boolean x -> do
    var <- fresh Output ReadBool WriteBool
    x' <- convertExprB x
    return [(var, ExprB x')]
  T.Field x -> do
    var <- fresh Output ReadField WriteField
    x' <- convertExprF x
    return [(var, ExprF x')]
  T.UInt x -> do
    x' <- convertExprU x
    var <- fresh Output (ReadUInt (widthOf x')) (WriteUInt (widthOf x'))
    return [(var, ExprU x')]
  T.Array exprs -> do
    exprss <- mapM convertExprAndAllocOutputVar exprs
    return (concat exprss)
  where
    fresh :: Category -> ReadType -> WriteType -> M n Var
    fresh category readType writeType = do
      counters <- get
      let index = getCount counters (category, readType)
      modify $ addCount (category, writeType) 1
      return index

convertExpr :: (GaloisField n, Integral n) => T.Expr -> M n [Expr n]
convertExpr expr = case expr of
  T.Unit -> return []
  T.Boolean x -> do
    x' <- convertExprB x
    return [ExprB x']
  T.Field x -> do
    x' <- convertExprF x
    return [ExprF x']
  T.UInt x -> do
    x' <- convertExprU x
    return [ExprU x']
  -- T.Var ref -> pure <$> convertRef3 ref
  T.Array exprs -> do
    exprss <- mapM convertExpr exprs
    return (concat exprss)

-- | Flatten and chain expressions with associative operator together when possible
chainExprsOfAssocOpAddF :: ExprF n -> ExprF n -> ExprF n
chainExprsOfAssocOpAddF x y = case (x, y) of
  (AddF x0 x1 xs, AddF y0 y1 ys) ->
    AddF x0 x1 (xs <> (y0 :<| y1 :<| ys))
  (AddF x0 x1 xs, _) ->
    AddF x0 x1 (xs |> y)
  (_, AddF y0 y1 ys) ->
    AddF x y0 (y1 :<| ys)
  -- there's nothing left we can do
  _ -> AddF x y mempty

chainExprsOfAssocOpAddU :: Width -> ExprU n -> Bool -> ExprU n -> Bool -> ExprU n
chainExprsOfAssocOpAddU w x xSign y ySign = case (x, y) of
  (AddU _ xs, AddU _ ys) ->
    AddU w (xs <> ys)
  (AddU _ xs, _) ->
    AddU w (xs |> (y, ySign))
  (_, AddU _ ys) ->
    AddU w ((x, xSign) :<| ys)
  -- there's nothing left we can do
  _ -> AddU w ((x, xSign) :<| (y, ySign) :<| mempty)

chainExprsOfAssocOpAndB :: ExprB n -> ExprB n -> ExprB n
chainExprsOfAssocOpAndB x y = case (x, y) of
  (AndB xs, AndB ys) ->
    AndB (xs <> ys)
  (AndB xs, _) ->
    AndB (xs |> y)
  (_, AndB ys) ->
    AndB (x :<| ys)
  -- there's nothing left we can do
  _ -> AndB (x :<| y :<| mempty)

chainExprsOfAssocOpAndU :: Width -> ExprU n -> ExprU n -> ExprU n
chainExprsOfAssocOpAndU w x y = case (x, y) of
  (AndU _ xs, AndU _ ys) ->
    AndU w (xs <> ys)
  (AndU _ xs, _) ->
    AndU w (xs |> y)
  (_, AndU _ ys) ->
    AndU w (x :<| ys)
  _ -> AndU w (x :<| y :<| mempty)

chainExprsOfAssocOpOrB :: ExprB n -> ExprB n -> ExprB n
chainExprsOfAssocOpOrB x y = case (x, y) of
  (OrB xs, OrB ys) ->
    OrB (xs <> ys)
  (OrB xs, _) ->
    OrB (xs |> y)
  (_, OrB ys) ->
    OrB (x :<| ys)
  -- there's nothing left we can do
  _ -> OrB (x :<| y :<| mempty)

chainExprsOfAssocOpXorB :: ExprB n -> ExprB n -> ExprB n
chainExprsOfAssocOpXorB x y = case (x, y) of
  (XorB xs, XorB ys) ->
    XorB (xs <> ys)
  (XorB xs, _) ->
    XorB (xs |> y)
  (_, XorB ys) ->
    XorB (x :<| ys)
  -- there's nothing left we can do
  _ -> XorB (x :<| y :<| mempty)

chainExprsOfAssocOpOrU :: Width -> ExprU n -> ExprU n -> ExprU n
chainExprsOfAssocOpOrU w x y = case (x, y) of
  (OrU _ xs, OrU _ ys) ->
    OrU w (xs <> ys)
  (OrU _ xs, _) ->
    OrU w (xs |> y)
  (_, OrU _ ys) ->
    OrU w (x :<| ys)
  -- there's nothing left we can do
  _ -> OrU w (x :<| y :<| mempty)

chainExprsOfAssocOpXorU :: Width -> ExprU n -> ExprU n -> ExprU n
chainExprsOfAssocOpXorU w x y = case (x, y) of
  (XorU _ xs, XorU _ ys) ->
    XorU w (xs <> ys)
  (XorU _ xs, _) ->
    XorU w (xs |> y)
  (_, XorU _ ys) ->
    XorU w (x :<| ys)
  -- there's nothing left we can do
  _ -> XorU w (x :<| y :<| mempty)
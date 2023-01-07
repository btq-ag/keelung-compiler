module Keelung.Compiler.Syntax.Erase (run) where

import Control.Monad.Reader
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.Sequence (Seq (..), (|>))
import Keelung.Compiler.Syntax.FieldBits (FieldBits (..))
import Keelung.Compiler.Syntax.Untyped
import Keelung.Data.Struct (Struct (..))
import Keelung.Syntax.Counters
import qualified Keelung.Syntax.Typed as T
import Keelung.Types

run :: (GaloisField n, Integral n) => T.Elaborated -> TypeErased n
run (T.Elaborated expr comp) =
  let T.Computation counters eb ebi assertions = comp
      proxy = 0
      numBitWidth = bitSize proxy
   in runM counters numBitWidth $ do
        -- start type erasure
        exprs <- eraseExprAndAllocOutputVar expr
        sameType proxy exprs
        assertions' <- concat <$> mapM eraseExpr assertions
        relations <-
          Relations mempty mempty
            <$> ( Struct
                    <$> mapM eraseExprF (structF eb)
                    <*> mapM eraseExprB (structB eb)
                    <*> mapM (mapM eraseExprU) (structU eb)
                )
            <*> ( Struct
                    <$> mapM eraseExprF (structF ebi)
                    <*> mapM eraseExprB (structB ebi)
                    <*> mapM (mapM eraseExprU) (structU ebi)
                )

        counters' <- get

        return $
          TypeErased
            { erasedExpr = exprs,
              erasedFieldBitWidth = numBitWidth,
              erasedCounters = counters',
              erasedRelations = relations,
              erasedAssertions = assertions'
            }
  where
    -- proxy trick for devising the bit width of field elements
    sameType :: n -> [(Var, Expr n)] -> M n ()
    sameType _ _ = return ()

--------------------------------------------------------------------------------

-- monad for collecting boolean vars along the way
type M n = StateT Counters (Reader Width)

runM :: Counters -> Width -> M n a -> a
runM counters width f = runReader (evalStateT f counters) width

--------------------------------------------------------------------------------

eraseExprB :: (GaloisField n, Integral n) => T.Boolean -> M n (ExprB n)
eraseExprB expr = case expr of
  T.ValB True -> return $ ValB 1
  T.ValB False -> return $ ValB 0
  T.VarB var -> return $ VarB var
  T.VarBI var -> return $ VarBI var
  T.AndB x y -> chainExprsOfAssocOpAndB <$> eraseExprB x <*> eraseExprB y
  T.OrB x y -> chainExprsOfAssocOpOrB <$> eraseExprB x <*> eraseExprB y
  T.XorB x y -> XorB <$> eraseExprB x <*> eraseExprB y
  T.NotB x -> NotB <$> eraseExprB x
  T.IfB p x y -> IfB <$> eraseExprB p <*> eraseExprB x <*> eraseExprB y
  T.EqB x y -> EqB <$> eraseExprB x <*> eraseExprB y
  T.EqF x y -> EqF <$> eraseExprF x <*> eraseExprF y
  T.EqU _ x y -> EqU <$> eraseExprU x <*> eraseExprU y
  T.BitU _ x i -> BitU <$> eraseExprU x <*> pure i

eraseExprF :: (GaloisField n, Integral n) => T.Field -> M n (ExprF n)
eraseExprF expr = case expr of
  T.ValF x -> return $ ValF (fromInteger x)
  T.ValFR x -> return $ ValF (fromRational x)
  T.VarF var -> return $ VarF var
  T.VarFI var -> return $ VarFI var
  T.AddF x y -> chainExprsOfAssocOpAddF <$> eraseExprF x <*> eraseExprF y
  T.SubF x y -> SubF <$> eraseExprF x <*> eraseExprF y
  T.MulF x y -> MulF <$> eraseExprF x <*> eraseExprF y
  T.DivF x y -> DivF <$> eraseExprF x <*> eraseExprF y
  T.IfF p x y -> IfF <$> eraseExprB p <*> eraseExprF x <*> eraseExprF y
  T.BtoF x -> BtoF <$> eraseExprB x

eraseExprU :: (GaloisField n, Integral n) => T.UInt -> M n (ExprU n)
eraseExprU expr = case expr of
  T.ValU w n -> return $ ValU w (fromIntegral n)
  T.VarU w var -> return $ VarU w var
  T.VarUI w var -> return $ VarUI w var
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

eraseExprAndAllocOutputVar :: (GaloisField n, Integral n) => T.Expr -> M n [(Var, Expr n)]
eraseExprAndAllocOutputVar expr = case expr of
  T.Unit -> return []
  T.Boolean x -> do
    var <- fresh OfOutput OfBoolean
    x' <- eraseExprB x
    return [(var, ExprB x')]
  T.Field x -> do
    var <- fresh OfOutput OfField
    x' <- eraseExprF x
    return [(var, ExprF x')]
  T.UInt x -> do
    x' <- eraseExprU x
    var <- fresh OfOutput (OfUInt (widthOfU x'))
    return [(var, ExprU x')]
  T.Array exprs -> do
    exprss <- mapM eraseExprAndAllocOutputVar exprs
    return (concat exprss)
  where
    fresh :: VarSort -> VarType -> M n Var
    fresh sort kind = do
      counters <- get
      let index = getCount sort kind counters
      modify $ addCount sort kind 1
      return index

eraseExpr :: (GaloisField n, Integral n) => T.Expr -> M n [Expr n]
eraseExpr expr = case expr of
  T.Unit -> return []
  T.Boolean x -> do
    x' <- eraseExprB x
    return [ExprB x']
  T.Field x -> do
    x' <- eraseExprF x
    return [ExprF x']
  T.UInt x -> do
    x' <- eraseExprU x
    return [ExprU x']
  -- T.Var ref -> pure <$> eraseRef3 ref
  T.Array exprs -> do
    exprss <- mapM eraseExpr exprs
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
{-# LANGUAGE TupleSections #-}

module Keelung.Compiler.Optimize.ConstantPropagation (run) where

import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Keelung.Compiler.Syntax.Untyped
import Keelung.Data.Struct (Struct (..))

--------------------------------------------------------------------------------

run :: (Integral n, GaloisField n) => TypeErased n -> TypeErased n
run (TypeErased exprs fieldWidth counters assertions sideEffects) = runM $ do
  sideEffects' <- mapM propagateSideEffect sideEffects
  TypeErased
    <$> mapM (\(var, expr) -> (var,) <$> propagateExpr expr) exprs
    <*> pure fieldWidth
    <*> pure counters
    <*> mapM propagateExpr assertions
    <*> pure sideEffects'

type Bindings n = Struct (IntMap n) (IntMap n) (IntMap n)

type M n = State (Bindings n)

runM :: State (Bindings n) a -> a
runM program = evalState program mempty

propagateSideEffect :: (Integral n, GaloisField n) => SideEffect n -> M n (SideEffect n)
propagateSideEffect sideEffect = case sideEffect of
  AssignmentF2 var val -> do
    val' <- propagateExprF val
    case val' of
      ValF v -> modify' $ \bindings -> bindings {structF = IntMap.insert var v (structF bindings)}
      _ -> return ()
    return $ AssignmentF2 var val'
  AssignmentB2 var val -> do
    val' <- propagateExprB val
    case val' of
      ValB v -> modify' $ \bindings -> bindings {structB = IntMap.insert var v (structB bindings)}
      _ -> return ()
    return $ AssignmentB2 var val'
  AssignmentU2 width var val -> do
    val' <- propagateExprU val
    case val' of
      ValU _ v -> modify' $ \bindings -> bindings {structU = IntMap.insertWith (<>) width (IntMap.singleton width v) (structU bindings)}
      _ -> return ()
    return $ AssignmentU2 width var val'
  DivMod width dividend divisor quotient remainder -> do
    dividend' <- propagateExprU dividend
    divisor' <- propagateExprU divisor
    quotient' <- propagateExprU quotient
    remainder' <- propagateExprU remainder
    return $ DivMod width dividend' divisor' quotient' remainder'

-- propagateSideEffect :: (Integral n, GaloisField n) => Relations n -> SideEffect n -> SideEffect n
-- propagateSideEffect relations (AssignmentF2 var val) = AssignmentF2 var (propagateExprF relations val)
-- propagateSideEffect relations (AssignmentB2 var val) = AssignmentB2 var (propagateExprB relations val)
-- propagateSideEffect relations (AssignmentU2 width var val) = AssignmentU2 width var (propagateExprU relations val)
-- propagateSideEffect relations (DivMod width dividend divisor quotient remainder) =
--   DivMod width (propagateExprU relations dividend) (propagateExprU relations divisor) (propagateExprU relations quotient) (propagateExprU relations remainder)

-- -- | Propagate constants in the relations, and return the fixed point of constant propagation
-- propagateRelations :: Relations n -> Relations n
-- propagateRelations before =
--   let (after, changed) = refineRelations before
--    in if changed
--         then propagateRelations after -- keep running
--         else after -- fixed point of 'refineResult'

-- | Seperate value bindings from expression bindings
-- refineRelations :: Relations n -> (Relations n, Bool)
-- refineRelations (Relations vals exprs) =
--   -- extract value bindings from expression bindings
--   let (fsV, fsE) = IntMap.mapEither seperateF (structF exprs)
--       (bsV, bsE) = IntMap.mapEither seperateB (structB exprs)
--       (usV, usE) = bimap IntMap.fromList IntMap.fromList $ unzip $ map (\(k, (a, b)) -> ((k, a), (k, b))) $ IntMap.toList $ fmap (IntMap.mapEither seperateU) (structU exprs)
--       changed = not $ IntMap.null fsV || IntMap.null bsV || IntMap.null usV
--    in ( Relations
--           ( vals
--               { structF = structF vals <> fsV,
--                 structB = structB vals <> bsV,
--                 structU = structU vals <> usV
--               }
--           )
--           (Struct fsE bsE usE),
--         changed
--       )
--   where
--     seperateF :: ExprF n -> Either n (ExprF n)
--     seperateF expr = case expr of
--       ValF val -> Left val
--       _ -> Right expr

--     seperateB :: ExprB n -> Either n (ExprB n)
--     seperateB expr = case expr of
--       ValB val -> Left val
--       _ -> Right expr

--     seperateU :: ExprU n -> Either n (ExprU n)
--     seperateU expr = case expr of
--       ValU _ val -> Left val
--       _ -> Right expr

-- constant propogation
propagateExpr :: (GaloisField n, Integral n) => Expr n -> M n (Expr n)
propagateExpr (ExprB x) = ExprB <$> propagateExprB x
propagateExpr (ExprF x) = ExprF <$> propagateExprF x
propagateExpr (ExprU x) = ExprU <$> propagateExprU x

propagateExprF :: ExprF n -> M n (ExprF n)
propagateExprF e = do
  bindings <- get
  case e of
    ValF _ -> return e
    VarF var -> case lookupF var bindings of
      Nothing -> return e
      Just val -> return (ValF val)
    VarFO _ -> return e -- no constant propagation for output variables
    VarFI _ -> return e -- no constant propagation for public input variables
    VarFP _ -> return e -- no constant propagation for private input variables
    SubF x y -> SubF <$> propagateExprF x <*> propagateExprF y
    AddF x y xs -> AddF <$> propagateExprF x <*> propagateExprF y <*> mapM propagateExprF xs
    MulF x y -> MulF <$> propagateExprF x <*> propagateExprF y
    DivF x y -> DivF <$> propagateExprF x <*> propagateExprF y
    IfF p x y -> IfF <$> propagateExprB p <*> propagateExprF x <*> propagateExprF y
    BtoF x -> BtoF <$> propagateExprB x

propagateExprU :: ExprU n -> M n (ExprU n)
propagateExprU e = do
  bindings <- get
  case e of
    ValU _ _ -> return e
    VarU w var -> case lookupU w var bindings of
      Nothing -> return e
      Just val -> return (ValU w val)
    VarUO _ _ -> return e -- no constant propagation for output variables
    VarUI _ _ -> return e -- no constant propagation for public input variables
    VarUP _ _ -> return e -- no constant propagation for private input variables
    SubU w x y -> SubU w <$> propagateExprU x <*> propagateExprU y
    AddU w x y -> AddU w <$> propagateExprU x <*> propagateExprU y
    MulU w x y -> MulU w <$> propagateExprU x <*> propagateExprU y
    AndU w x y xs -> AndU w <$> propagateExprU x <*> propagateExprU y <*> mapM propagateExprU xs
    OrU w x y xs -> OrU w <$> propagateExprU x <*> propagateExprU y <*> mapM propagateExprU xs
    XorU w x y -> XorU w <$> propagateExprU x <*> propagateExprU y
    NotU w x -> NotU w <$> propagateExprU x
    IfU w p x y -> IfU w <$> propagateExprB p <*> propagateExprU x <*> propagateExprU y
    RoLU w i x -> RoLU w i <$> propagateExprU x
    ShLU w i x -> ShLU w i <$> propagateExprU x
    SetU w x i b -> SetU w <$> propagateExprU x <*> pure i <*> propagateExprB b
    BtoU w x -> BtoU w <$> propagateExprB x

propagateExprB :: ExprB n -> M n (ExprB n)
propagateExprB e = do
  bindings <- get
  case e of
    ValB _ -> return e
    VarB var -> case lookupB var bindings of
      Nothing -> return e
      Just val -> return (ValB val)
    VarBO _ -> return e -- no constant propagation for output variables
    VarBI _ -> return e -- no constant propagation for public input variables
    VarBP _ -> return e -- no constant propagation for private input variables
    AndB x y xs -> AndB <$> propagateExprB x <*> propagateExprB y <*> mapM propagateExprB xs
    OrB x y xs -> OrB <$> propagateExprB x <*> propagateExprB y <*> mapM propagateExprB xs
    XorB x y -> XorB <$> propagateExprB x <*> propagateExprB y
    NotB x -> NotB <$> propagateExprB x
    IfB p x y -> IfB <$> propagateExprB p <*> propagateExprB x <*> propagateExprB y
    NEqB x y -> NEqB <$> propagateExprB x <*> propagateExprB y
    NEqF x y -> NEqF <$> propagateExprF x <*> propagateExprF y
    NEqU x y -> NEqU <$> propagateExprU x <*> propagateExprU y
    EqB x y -> EqB <$> propagateExprB x <*> propagateExprB y
    EqF x y -> EqF <$> propagateExprF x <*> propagateExprF y
    EqU x y -> EqU <$> propagateExprU x <*> propagateExprU y
    BitU x i -> BitU <$> propagateExprU x <*> pure i

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Replace case with maybe" #-}
module Keelung.Compiler.Optimize.ConstantPropagation (run) where

import Data.Bifunctor (Bifunctor (second), bimap)
import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict qualified as IntMap
import Keelung.Compiler.Syntax.Untyped
import Keelung.Data.Struct (Struct (..))

--------------------------------------------------------------------------------

-- 1. Propagate constants in Relations
-- 2. Propagate constant in the output expression
-- 3. Propagate constant in assertions
run :: (Integral n, GaloisField n) => TypeErased n -> TypeErased n
run (TypeErased exprs fieldWidth counters oldRelations assertions divModRelsU sideEffects) =
  let newRelations = propagateRelations oldRelations
      exprs' = map (second (propagateConstant newRelations)) exprs
      newAssertions = map (propagateConstant newRelations) assertions
      newDivModRels =
        fmap
          -- dividend = divisor * quotient + remainder
          ( fmap
              ( \(dividend, divisor, quotient, remainder) ->
                  ( propagateExprU newRelations dividend,
                    propagateExprU newRelations divisor,
                    propagateExprU newRelations quotient,
                    propagateExprU newRelations remainder
                  )
              )
          )
          divModRelsU

      newSideEffects = fmap (propagateSideEffect newRelations) sideEffects
   in -- newSide
      TypeErased exprs' fieldWidth counters newRelations newAssertions newDivModRels newSideEffects

propagateSideEffect :: (Integral n, GaloisField n) => Relations n -> SideEffect n -> SideEffect n
propagateSideEffect relations (AssignmentF2 var val) = AssignmentF2 var (propagateExprF relations val)
propagateSideEffect relations (AssignmentB2 var val) = AssignmentB2 var (propagateExprB relations val)
propagateSideEffect relations (AssignmentU2 width var val) = AssignmentU2 width var (propagateExprU relations val)
propagateSideEffect relations (DivMod width dividend divisor quotient remainder) =
  DivMod width (propagateExprU relations dividend) (propagateExprU relations divisor) (propagateExprU relations quotient) (propagateExprU relations remainder)

-- | Propagate constants in the relations, and return the fixed point of constant propagation
propagateRelations :: Relations n -> Relations n
propagateRelations before =
  let (after, changed) = refineRelations before
   in if changed
        then propagateRelations after -- keep running
        else after -- fixed point of 'refineResult'

-- | Seperate value bindings from expression bindings
refineRelations :: Relations n -> (Relations n, Bool)
refineRelations (Relations vals exprs) =
  -- extract value bindings from expression bindings
  let (fsV, fsE) = IntMap.mapEither seperateF (structF exprs)
      (bsV, bsE) = IntMap.mapEither seperateB (structB exprs)
      (usV, usE) = bimap IntMap.fromList IntMap.fromList $ unzip $ map (\(k, (a, b)) -> ((k, a), (k, b))) $ IntMap.toList $ fmap (IntMap.mapEither seperateU) (structU exprs)
      changed = not $ IntMap.null fsV || IntMap.null bsV || IntMap.null usV
   in ( Relations
          ( vals
              { structF = structF vals <> fsV,
                structB = structB vals <> bsV,
                structU = structU vals <> usV
              }
          )
          (Struct fsE bsE usE),
        changed
      )
  where
    seperateF :: ExprF n -> Either n (ExprF n)
    seperateF expr = case expr of
      ValF val -> Left val
      _ -> Right expr

    seperateB :: ExprB n -> Either n (ExprB n)
    seperateB expr = case expr of
      ValB val -> Left val
      _ -> Right expr

    seperateU :: ExprU n -> Either n (ExprU n)
    seperateU expr = case expr of
      ValU _ val -> Left val
      _ -> Right expr

-- constant propogation
propagateConstant :: (GaloisField n, Integral n) => Relations n -> Expr n -> Expr n
propagateConstant relations (ExprB x) = ExprB (propagateExprB relations x)
propagateConstant relations (ExprF x) = ExprF (propagateExprF relations x)
propagateConstant relations (ExprU x) = ExprU (propagateExprU relations x)

propagateExprF :: Relations n -> ExprF n -> ExprF n
propagateExprF relations e = case e of
  ValF _ -> e
  VarF var -> case lookupF var (valueBindings relations) of
    Nothing -> e
    Just val -> ValF val
  VarFO _ -> e -- no constant propagation for output variables
  VarFI _ -> e -- no constant propagation for public input variables
  VarFP _ -> e -- no constant propagation for private input variables
  SubF x y -> SubF (propagateExprF relations x) (propagateExprF relations y)
  AddF x y xs -> AddF (propagateExprF relations x) (propagateExprF relations y) (fmap (propagateExprF relations) xs)
  MulF x y -> MulF (propagateExprF relations x) (propagateExprF relations y)
  DivF x y -> DivF (propagateExprF relations x) (propagateExprF relations y)
  IfF p x y -> IfF (propagateExprB relations p) (propagateExprF relations x) (propagateExprF relations y)
  BtoF x -> BtoF (propagateExprB relations x)

propagateExprU :: Relations n -> ExprU n -> ExprU n
propagateExprU relations e = case e of
  ValU _ _ -> e
  VarU w var -> case lookupU w var (valueBindings relations) of
    Nothing -> e
    Just val -> ValU w val
  VarUO _ _ -> e -- no constant propagation for output variables
  VarUI _ _ -> e -- no constant propagation for public input variables
  VarUP _ _ -> e -- no constant propagation for private input variables
  SubU w x y -> SubU w (propagateExprU relations x) (propagateExprU relations y)
  AddU w x y -> AddU w (propagateExprU relations x) (propagateExprU relations y)
  MulU w x y -> MulU w (propagateExprU relations x) (propagateExprU relations y)
  AndU w x y xs -> AndU w (propagateExprU relations x) (propagateExprU relations y) (fmap (propagateExprU relations) xs)
  OrU w x y xs -> OrU w (propagateExprU relations x) (propagateExprU relations y) (fmap (propagateExprU relations) xs)
  XorU w x y -> XorU w (propagateExprU relations x) (propagateExprU relations y)
  NotU w x -> NotU w (propagateExprU relations x)
  IfU w p x y -> IfU w (propagateExprB relations p) (propagateExprU relations x) (propagateExprU relations y)
  RoLU w i x -> RoLU w i (propagateExprU relations x)
  ShLU w i x -> ShLU w i (propagateExprU relations x)
  SetU w x i b -> SetU w (propagateExprU relations x) i (propagateExprB relations b)
  BtoU w x -> BtoU w (propagateExprB relations x)

propagateExprB :: Relations n -> ExprB n -> ExprB n
propagateExprB relations e = case e of
  ValB _ -> e
  VarB var -> case lookupB var (valueBindings relations) of
    Nothing -> e
    Just val -> ValB val
  VarBO _ -> e -- no constant propagation for output variables
  VarBI _ -> e -- no constant propagation for public input variables
  VarBP _ -> e -- no constant propagation for private input variables
  AndB x y xs -> AndB (propagateExprB relations x) (propagateExprB relations y) (fmap (propagateExprB relations) xs)
  OrB x y xs -> OrB (propagateExprB relations x) (propagateExprB relations y) (fmap (propagateExprB relations) xs)
  XorB x y -> XorB (propagateExprB relations x) (propagateExprB relations y)
  NotB x -> NotB (propagateExprB relations x)
  IfB p x y -> IfB (propagateExprB relations p) (propagateExprB relations x) (propagateExprB relations y)
  NEqB x y -> NEqB (propagateExprB relations x) (propagateExprB relations y)
  NEqF x y -> NEqF (propagateExprF relations x) (propagateExprF relations y)
  NEqU x y -> NEqU (propagateExprU relations x) (propagateExprU relations y)
  EqB x y -> EqB (propagateExprB relations x) (propagateExprB relations y)
  EqF x y -> EqF (propagateExprF relations x) (propagateExprF relations y)
  EqU x y -> EqU (propagateExprU relations x) (propagateExprU relations y)
  BitU x i -> BitU (propagateExprU relations x) i

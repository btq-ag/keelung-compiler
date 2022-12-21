{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Replace case with maybe" #-}
module Keelung.Compiler.Optimize.ConstantPropagation (run) where

import Data.Bifunctor (bimap)
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap.Strict as IntMap
import Keelung.Compiler.Syntax.Untyped

--------------------------------------------------------------------------------

-- 1. Propagate constants in Relations
-- 2. Propagate constant in the output expression
-- 3. Propagate constant in assertions
run :: (Integral n, GaloisField n) => TypeErased n -> TypeErased n
run (TypeErased expr fieldWidth counters oldRelations assertions assignments) =
  let newRelations = propagateRelations oldRelations
      expr' = propagateConstant newRelations <$> expr
      newAssertions = map (propagateConstant newRelations) assertions
   in TypeErased expr' fieldWidth counters newRelations newAssertions assignments

data Result n
  = Result
      (Bindings n) -- extracted bindings of values after propagation
      (Bindings (Expr n)) -- bindings of expressions waiting to be processed

-- | Propagate constants in the relations, and return the fixed point of constant propagation
propagateRelations :: Relations n -> Relations n
propagateRelations = toRelations . go . fromRelations
  where
    go :: Result n -> Result n
    go before =
      let (after, changed) = refineResult before
       in if changed
            then go after -- keep running
            else after -- fixed point of 'refineResult'
    toRelations :: Result n -> Relations n
    toRelations (Result vbs ebs) = Relations vbs ebs

    fromRelations :: Relations n -> Result n
    fromRelations (Relations vbs ebs) = Result vbs ebs

-- | Seperate value bindings from expression bindings
refineResult :: Result n -> (Result n, Bool)
refineResult (Result vals exprs) =
  -- extract value bindings from expression bindings
  let (fsV, fsE) = IntMap.mapEither seperateF (bindingsF exprs)
      (fisV, fisE) = IntMap.mapEither seperateF (bindingsFI exprs)
      (bsV, bsE) = IntMap.mapEither seperateB (bindingsB exprs)
      (bisV, bisE) = IntMap.mapEither seperateB (bindingsBI exprs)
      (usV, usE) = bimap IntMap.fromList IntMap.fromList $ unzip $ map (\(k, (a, b)) -> ((k, a), (k, b))) $ IntMap.toList $ fmap (IntMap.mapEither seperateU) (bindingsUs exprs)
      (uisV, uisE) = bimap IntMap.fromList IntMap.fromList $ unzip $ map (\(k, (a, b)) -> ((k, a), (k, b))) $ IntMap.toList $ fmap (IntMap.mapEither seperateU) (bindingsUIs exprs)
      changed = not $ IntMap.null fsV || IntMap.null fisV || IntMap.null bsV || IntMap.null bisV || IntMap.null usV || IntMap.null uisV
   in ( Result
          ( vals
              { bindingsF = bindingsF vals <> fsV,
                bindingsFI = bindingsFI vals <> fisV,
                bindingsB = bindingsB vals <> bsV,
                bindingsBI = bindingsBI vals <> bisV,
                bindingsUs = bindingsUs vals <> usV,
                bindingsUIs = bindingsUIs vals <> uisV
              }
          )
          (Bindings fsE fisE bsE bisE usE uisE),
        changed
      )
  where
    seperateF :: Expr n -> Either n (Expr n)
    seperateF expr = case expr of
      ExprF (ValF val) -> Left val
      ExprU _ -> error "[ panic ] UInt expression in Field bindings of expressions"
      ExprB _ -> error "[ panic ] Boolean expression in Field bindings of expressions"
      _ -> Right expr

    seperateB :: Expr n -> Either n (Expr n)
    seperateB expr = case expr of
      ExprF _ -> error "[ panic ] Field value in Boolean bindings of expressions"
      ExprU _ -> error "[ panic ] UInt expression in Boolean bindings of expressions"
      ExprB (ValB val) -> Left val
      _ -> Right expr

    seperateU :: Expr n -> Either n (Expr n)
    seperateU expr = case expr of
      ExprF _ -> error "[ panic ] Field value in UInt bindings of expressions"
      ExprU (ValU _ val) -> Left val
      ExprB _ -> error "[ panic ] Boolean value in UInt bindings of expressions"
      _ -> Right expr

-- constant propogation
propagateConstant :: (GaloisField n, Integral n) => Relations n -> Expr n -> Expr n
propagateConstant relations = propagate
  where
    propagateF e = case e of
      ValF _ -> e
      VarF var -> case lookupF var (valueBindings relations) of
        Nothing -> e
        Just val -> ValF val
      VarFO _ -> e -- no constant propagation for output variables
      VarFI _ -> e -- no constant propagation for input variables
      SubF x y -> SubF (propagateF x) (propagateF y)
      AddF x y xs -> AddF (propagateF x) (propagateF y) (fmap propagateF xs)
      MulF x y -> MulF (propagateF x) (propagateF y)
      DivF x y -> DivF (propagateF x) (propagateF y)
      IfF p x y -> IfF (propagateB p) (propagateF x) (propagateF y)
      BtoF x -> BtoF (propagateB x)

    propagateU e = case e of
      ValU _ _ -> e
      VarU w var -> case lookupU w var (valueBindings relations) of
        Nothing -> e
        Just val -> ValU w val
      OutputVarU _ _ -> e -- no constant propagation for output variables
      InputVarU _ _ -> e -- no constant propagation for input variables
      SubU w x y -> SubU w (propagateU x) (propagateU y)
      AddU w x y -> AddU w (propagateU x) (propagateU y)
      MulU w x y -> MulU w (propagateU x) (propagateU y)
      AndU w x y xs -> AndU w (propagateU x) (propagateU y) (fmap propagateU xs)
      OrU w x y xs -> OrU w (propagateU x) (propagateU y) (fmap propagateU xs)
      XorU w x y -> XorU w (propagateU x) (propagateU y)
      NotU w x -> NotU w (propagateU x)
      IfU w p x y -> IfU w (propagateB p) (propagateU x) (propagateU y)
      RoLU w i x -> RoLU w i (propagateU x)
      ShLU w i x -> ShLU w i (propagateU x)
      BtoU w x -> BtoU w (propagateB x)

    propagateB e = case e of
      ValB _ -> e
      VarB var -> case lookupB var (valueBindings relations) of
        Nothing -> e
        Just val -> ValB val
      OutputVarB _ -> e -- no constant propagation for output variables
      InputVarB _ -> e -- no constant propagation for input variables
      AndB x y xs -> AndB (propagateB x) (propagateB y) (fmap propagateB xs)
      OrB x y xs -> OrB (propagateB x) (propagateB y) (fmap propagateB xs)
      XorB x y -> XorB (propagateB x) (propagateB y)
      NotB x -> NotB (propagateB x)
      IfB p x y -> IfB (propagateB p) (propagateB x) (propagateB y)
      NEqB x y -> NEqB (propagateB x) (propagateB y)
      NEqF x y -> NEqF (propagateF x) (propagateF y)
      NEqU x y -> NEqU (propagateU x) (propagateU y)
      EqB x y -> EqB (propagateB x) (propagateB y)
      EqF x y -> EqF (propagateF x) (propagateF y)
      EqU x y -> EqU (propagateU x) (propagateU y)
      BitU x i -> BitU (propagateU x) i

    propagate e = case e of
      ExprF x -> ExprF (propagateF x)
      ExprU x -> ExprU (propagateU x)
      ExprB x -> ExprB (propagateB x)
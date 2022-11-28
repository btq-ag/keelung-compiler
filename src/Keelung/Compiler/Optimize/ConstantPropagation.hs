{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Replace case with maybe" #-}
module Keelung.Compiler.Optimize.ConstantPropagation (run) where

import Data.Field.Galois (GaloisField)
import qualified Data.IntMap.Strict as IntMap
import Keelung.Compiler.Syntax.Untyped
import qualified Data.Map.Strict as Map
import Keelung.Compiler.Constraint2

--------------------------------------------------------------------------------

-- 1. Propagate constant in bindings of expressions
-- 2. Propagate constant in the expression and assertions
run :: (Integral n, GaloisField n) => TypeErased n -> TypeErased n
run (TypeErased expr fieldWidth countersOld counters oldRelations assertions assignments numBinReps customBinReps) =
  let newRelations = propagateRelations oldRelations
      expr' = propagateConstant newRelations <$> expr
      newAssertions = map (propagateConstant newRelations) assertions
   in TypeErased expr' fieldWidth countersOld counters newRelations newAssertions assignments numBinReps customBinReps

data Result n
  = Result
      Int -- number of entries in the extracted bindings of values
      (Bindings n) -- extracted bindings of values after propagation
      (Bindings (Expr n)) -- bindings of expressions waiting to be processed

-- |
propagateRelations :: Relations n -> Relations n
propagateRelations = toRelations . go . fromRelations
  where
    go :: Result n -> Result n
    go (Result n vbs ebs) =
      let (Result n' vbs' ebs') = refineResult (Result n vbs ebs)
       in if n' == n
            then Result n' vbs' ebs' -- fixed point of 'refineResult'
            else go (Result n' vbs' ebs') -- keep running
    toRelations :: Result n -> Relations n
    toRelations (Result _ vbs ebs) = Relations vbs ebs

    fromRelations :: Relations n -> Result n
    fromRelations (Relations vbs ebs) = Result 0 vbs ebs

-- | Seperate value bindings from expression bindings
refineResult :: Result n -> Result n
refineResult result@(Result _ _ (Bindings ns bs us)) =
  handleU (handleB (handleN result ns) bs) us
  where
    handleN =
      Map.foldlWithKey'
        ( \(Result n vbs ebs) var expr ->
            case expr of
              ExprN (ValN _ val) -> Result (succ n) (insertN var val vbs) ebs
              ExprU _ -> error "[ panic ] UInt expression in Number bindings of expressions"
              ExprB _ -> error "[ panic ] Boolean expression in Number bindings of expressions"
              _ -> Result n vbs (insertN var expr ebs)
        )
    handleB =
      Map.foldlWithKey'
        ( \(Result n vbs ebs) var expr ->
            case expr of
              ExprN _ -> error "[ panic ] Number value in Number bindings of expressions"
              ExprU _ -> error "[ panic ] UInt expression in Number bindings of expressions"
              ExprB (ValB val) -> Result (succ n) (insertB var val vbs) ebs
              _ -> Result n vbs (insertB var expr ebs)
        )
    handleU =
      IntMap.foldlWithKey'
        ( \result' width mapping ->
            Map.foldlWithKey'
              ( \(Result n' vbs' ebs') var expr ->
                  case expr of
                    ExprN _ -> error "[ panic ] Number value in Number bindings of expressions"
                    ExprU (ValU _ val) -> Result (succ n') (insertU width var val vbs') ebs'
                    ExprB _ -> error "[ panic ] Boolean value in Number bindings of expressions"
                    _ -> Result n' vbs' (insertU width var expr ebs')
              )
              result'
              mapping
        )

-- constant propogation
propagateConstant :: (GaloisField n, Integral n) => Relations n -> Expr n -> Expr n
propagateConstant relations = propagate
  where
    propagateN e = case e of
      ValN _ _ -> e
      VarN w var -> case lookupN (RefF var) (valueBindings relations) of
        Nothing -> e
        Just val -> ValN w val
      OutputVarN _ _ -> e -- no constant propagation for output variables
      InputVarN _ _ -> e -- no constant propagation for input variables
      SubN w x y -> SubN w (propagateN x) (propagateN y)
      AddN w x y xs -> AddN w (propagateN x) (propagateN y) (fmap propagateN xs)
      MulN w x y -> MulN w (propagateN x) (propagateN y)
      DivN w x y -> DivN w (propagateN x) (propagateN y)
      IfN w p x y -> IfN w (propagateB p) (propagateN x) (propagateN y)
      BtoN w x -> BtoN w (propagateB x)

    propagateU e = case e of
      ValU _ _ -> e
      VarU w var -> case lookupU w (RefU w var) (valueBindings relations) of
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
      BtoU w x -> BtoU w (propagateB x)

    propagateB e = case e of
      ValB _ -> e
      VarB var -> case lookupB (RefB var) (valueBindings relations) of
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
      NEqN x y -> NEqN (propagateN x) (propagateN y)
      NEqU x y -> NEqU (propagateU x) (propagateU y)
      EqB x y -> EqB (propagateB x) (propagateB y)
      EqN x y -> EqN (propagateN x) (propagateN y)
      EqU x y -> EqU (propagateU x) (propagateU y)
      BitU x i -> BitU (propagateU x) i

    propagate e = case e of
      ExprN x -> ExprN (propagateN x)
      ExprU x -> ExprU (propagateU x)
      ExprB x -> ExprB (propagateB x)
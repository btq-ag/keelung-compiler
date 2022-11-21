module Keelung.Compiler.Optimize.ConstantPropagation (run) where

import Data.Field.Galois (GaloisField)
import qualified Data.IntMap.Strict as IntMap
import Keelung.Compiler.Syntax.Untyped

--------------------------------------------------------------------------------

-- 1. Propagate constant in bindings of expressions
-- 2. Propagate constant in the expression and assertions
run :: (Integral n, GaloisField n) => TypeErased n -> TypeErased n
run (TypeErased expr counters oldRelations assertions assignments numBinReps customBinReps) =
  let newRelations = propagateRelations oldRelations
      expr' = propagateConstant newRelations <$> expr
      newAssertions = map (propagateConstant newRelations) assertions
   in TypeErased expr' counters newRelations newAssertions assignments numBinReps customBinReps

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
      IntMap.foldlWithKey'
        ( \(Result n vbs ebs) var expr ->
            case expr of
              Number _ val -> Result (succ n) (insertN var val vbs) ebs
              UInt _ _ -> error "[ panic ] UInt value in Number bindings of expressions"
              Boolean _ -> error "[ panic ] Boolean value in Number bindings of expressions"
              _ -> Result n vbs (insertN var expr ebs)
        )
    handleB =
      IntMap.foldlWithKey'
        ( \(Result n vbs ebs) var expr ->
            case expr of
              Number _ _ -> error "[ panic ] Number value in Number bindings of expressions"
              UInt _ _ -> error "[ panic ] UInt value in Number bindings of expressions"
              Boolean val -> Result (succ n) (insertB var val vbs) ebs
              _ -> Result n vbs (insertB var expr ebs)
        )
    handleU =
      IntMap.foldlWithKey'
        ( \result' width mapping ->
            IntMap.foldlWithKey'
              ( \(Result n' vbs' ebs') var expr ->
                  case expr of
                    Number _ _ -> error "[ panic ] Number value in Number bindings of expressions"
                    UInt _ val -> Result (succ n') (insertU width var val vbs') ebs'
                    Boolean _ -> error "[ panic ] Boolean value in Number bindings of expressions"
                    _ -> Result n' vbs' (insertU width var expr ebs')
              )
              result'
              mapping
        )

-- constant propogation
propagateConstant :: (GaloisField n, Integral n) => Relations n -> Expr n -> Expr n
propagateConstant relations = propogate
  where
    propogate e = case e of
      Number _ _ -> e
      UInt _ _ -> e
      Boolean _ -> e
      Var bw var -> case bw of
        BWNumber w -> case lookupN var (valueBindings relations) of
          Nothing -> Var bw var
          Just val -> Number w val
        BWBoolean -> case lookupB var (valueBindings relations) of
          Nothing -> Var bw var
          Just val -> Boolean val
        BWUInt w -> case lookupU w var (valueBindings relations) of
          Nothing -> Var bw var
          Just val -> UInt w val
        BWUnit -> Var bw var
      UVar w var -> case lookupU w var (valueBindings relations) of
        Nothing -> Var (BWUInt w) var
        Just val -> UInt w val
      Rotate w n x -> Rotate w n (propogate x)
      NAryOp w op x y es -> NAryOp w op (propogate x) (propogate y) (fmap propogate es)
      BinaryOp w op x y -> BinaryOp w op (propogate x) (propogate y)
      If w p x y -> If w (propogate p) (propogate x) (propogate y)
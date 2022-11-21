module Keelung.Compiler.Optimize.ConstantPropagation (run) where

import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Syntax.Untyped

--------------------------------------------------------------------------------

-- 1. Propagate constant in assignments
-- 2. Propagate constant in the expression and assertions
run :: (Integral n, GaloisField n) => TypeErased n -> TypeErased n
run (TypeErased expr counters oldRelations assertions assignments numBinReps customBinReps) =
  let (newRelations, newAssignments) = propagateInAssignments oldRelations assignments
      expr' = propagateConstant newRelations <$> expr
      newAssertions = map (propagateConstant newRelations) assertions
   in TypeErased expr' counters newRelations newAssertions newAssignments numBinReps customBinReps

-- Propagate constant in assignments and return the relations for later use
-- 1. extract relations from assignments
-- 2. propagate constant in assignments
propagateInAssignments :: (Integral n, GaloisField n) => Relations n -> [Assignment n] -> (Relations n, [Assignment n])
propagateInAssignments oldRelations xs =
  let (newRelations, assignments) = extractRelations xs
      combinedRelations = oldRelations <> newRelations
      assignments' =
        map
          ( \(Assignment var expr) ->
              Assignment var (propagateConstant combinedRelations expr)
          )
          assignments
   in (combinedRelations, assignments')

-- Extract bindings of constant values, collect them
-- and returns the rest of the assignments
extractRelations :: [Assignment n] -> (Relations n, [Assignment n])
extractRelations = go mempty []
  where
    go :: Relations n -> [Assignment n] -> [Assignment n] -> (Relations n, [Assignment n])
    go relation rest [] = (relation, rest)
    go relation rest (Assignment var (Number _ val) : xs) =
      go (relation {valueBindings = insertN var val (valueBindings relation)}) rest xs
    go relation rest (Assignment var (UInt w val) : xs) =
      go (relation {valueBindings = insertU w var val (valueBindings relation)}) rest xs
    go relation rest (Assignment var (Boolean val) : xs) =
      go (relation {valueBindings = insertB var val (valueBindings relation)}) rest xs
    go relation rest (others : xs) = go relation (others : rest) xs

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
      UVar w var -> case lookupU w var (valueBindings relations) of
        Nothing -> Var (BWUInt w) var
        Just val -> UInt w val
      Rotate w n x -> Rotate w n (propogate x)
      NAryOp w op x y es -> NAryOp w op (propogate x) (propogate y) (fmap propogate es)
      BinaryOp w op x y -> BinaryOp w op (propogate x) (propogate y)
      If w p x y -> If w (propogate p) (propogate x) (propogate y)
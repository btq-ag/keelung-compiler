module Keelung.Compiler.Optimize.ConstantPropagation (run) where

import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Keelung.Compiler.Syntax.Untyped

--------------------------------------------------------------------------------

-- 1. Propagate constant in assignments
-- 2. Propagate constant in the expression and assertions
run :: (Integral n, GaloisField n) => TypeErased n -> TypeErased n
run (TypeErased expr counters assertions assignments numBinReps customBinReps) =
  let (bindings, assignments') = propagateInAssignments assignments
      expr' = propagateConstant bindings <$> expr
      assertions' = map (propagateConstant bindings) assertions

      assignments'' = assignments' <> map (\(var, (w, val)) -> Assignment var (Val w val)) (IntMap.toList bindings)
   in TypeErased expr' counters assertions' assignments'' numBinReps customBinReps

-- Propagate constant in assignments and return the bindings for later use
propagateInAssignments :: (Integral n, GaloisField n) => [Assignment n] -> (IntMap (BitWidth, n), [Assignment n])
propagateInAssignments xs =
  let (bindings, assignments) = extractBindings xs
      assignments' =
        map
          ( \(Assignment var expr) ->
              Assignment var (propagateConstant bindings expr)
          )
          assignments
   in (bindings, assignments')

-- Extract bindings of constant values and collect them as an IntMap
-- and returns the rest of the assignments
extractBindings :: [Assignment n] -> (IntMap (BitWidth, n), [Assignment n])
extractBindings = go IntMap.empty []
  where
    go :: IntMap (BitWidth, n) -> [Assignment n] -> [Assignment n] -> (IntMap (BitWidth, n), [Assignment n])
    go bindings rest [] = (bindings, rest)
    go bindings rest (Assignment var (Val w val) : xs) =
      go (IntMap.insert var (w, val) bindings) rest xs
    go bindings rest (others : xs) = go bindings (others : rest) xs

-- constant propogation
propagateConstant :: (GaloisField n, Integral n) => IntMap (BitWidth, n) -> Expr n -> Expr n
propagateConstant bindings = propogate
  where
    propogate e = case e of
      Val _ _ -> e
      Var w var -> case IntMap.lookup var bindings of
        Nothing -> Var w var
        Just (_, val) -> Val w val
      Rotate w n x -> Rotate w n (propogate x)
      NAryOp w op x y es -> NAryOp w op (propogate x) (propogate y) (fmap propogate es)
      BinaryOp w op x y -> BinaryOp w op (propogate x) (propogate y)
      If w p x y -> If w (propogate p) (propogate x) (propogate y)
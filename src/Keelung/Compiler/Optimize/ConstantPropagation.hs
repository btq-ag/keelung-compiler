module Keelung.Compiler.Optimize.ConstantPropagation (run) where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Keelung.Compiler.Syntax.Untyped

--------------------------------------------------------------------------------

-- 1. Propagate constant in assignments
-- 2. Propagate constant in the expression and assertions
run :: TypeErased n -> TypeErased n
run (TypeErased expr assertions assignments allVarSize inputVarSize outputVarSize boolVars) =
  let (bindings, assignments') = propagateInAssignments assignments
      expr' = propagateConstant bindings <$> expr
      assertions' = map (propagateConstant bindings) assertions

      assignments'' = assignments' <> map (\(var, val) -> Assignment var (Val val)) (IntMap.toList bindings)
   in TypeErased expr' assertions' assignments'' allVarSize inputVarSize outputVarSize boolVars

-- Propagate constant in assignments and return the bindings for later use
propagateInAssignments :: [Assignment n] -> (IntMap n, [Assignment n])
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
extractBindings :: [Assignment n] -> (IntMap n, [Assignment n])
extractBindings = go IntMap.empty []
  where
    go :: IntMap n -> [Assignment n] -> [Assignment n] -> (IntMap n, [Assignment n])
    go bindings rest [] = (bindings, rest)
    go bindings rest (Assignment var (Val val) : xs) =
      go (IntMap.insert var val bindings) rest xs
    go bindings rest (others : xs) = go bindings (others : rest) xs

-- constant propogation
propagateConstant :: IntMap a -> Expr a -> Expr a
propagateConstant bindings = propogate
  where
    propogate e = case e of
      Var var -> lookupVar var
      Val _ -> e
      BinOp op es -> BinOp op (fmap propogate es)
      If p x y -> If (propogate p) (propogate x) (propogate y)

    lookupVar var = case IntMap.lookup var bindings of
      Nothing -> Var var
      Just val -> Val val
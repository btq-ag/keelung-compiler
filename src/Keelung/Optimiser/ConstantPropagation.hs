module Keelung.Optimiser.ConstantPropagation where

-- import Data.IntMap (IntMap)
-- import Keelung.Syntax.Untyped
-- import Keelung.Constraint

--------------------------------------------------------------------------------

-- run :: ConstraintSystem n -> ConstraintSystem n
-- run (ConstraintSystem set numVars inputVars outputVar) = _wa


-- -- constant propogation
-- propogateConstant :: IntMap a -> Expr a -> Expr a
-- propogateConstant bindings = propogate
--   where
--     propogate e = case e of
--       Var var -> lookupVar var
--       Val _ -> e
--       BinOp op es -> BinOp op (map propogate es)
--       IfThenElse p x y -> IfThenElse (propogate p) (propogate x) (propogate y)

--     lookupVar var = case IntMap.lookup var bindings of
--       Nothing -> Var var
--       Just val -> Val val
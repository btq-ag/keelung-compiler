{-# LANGUAGE BangPatterns #-}

module Keelung.Optimise.MinimiseConstraints (run, substConstraint) where

import Control.Monad
import Data.Field.Galois (GaloisField)
import Data.Set (Set)
import qualified Data.Set as Set
import Keelung.Constraint (Constraint (..), cadd)
import qualified Keelung.Constraint.CoeffMap as CoeffMap
import Keelung.Optimise.Monad
import Keelung.Syntax.Common (Var)

run ::
  (GaloisField n, Bounded n, Integral n) =>
  [Var] ->
  Set (Constraint n) ->
  OptiM n (Set (Constraint n))
run pinnedVars constraints = do
  minimised <- minimiseManyTimes constraints
  -- -- substitute roots/constants in constraints
  -- substituted <- mapM substConstraint $ Set.toList simplified
  -- -- keep only constraints that is not tautologous

  -- removedTautology <- filterM (fmap not . isTautology) substituted

  pinned <- handlePinnedVars pinnedVars
   
  return (Set.fromList pinned <> minimised)

minimiseManyTimes ::
  (GaloisField n, Bounded n, Integral n) =>
  -- | Initial constraint set
  Set (Constraint n) ->
  -- | Resulting simplified constraint set
  OptiM n (Set (Constraint n))
minimiseManyTimes constraints = do
  constraints' <- minimiseOnce constraints
  let hasShrunk = Set.size constraints' < Set.size constraints
  let hasChanged = not $ Set.null (Set.difference constraints constraints')
  -- keep minimising if the constraints have shrunk or changed 
  if hasShrunk || hasChanged
    then minimiseManyTimes constraints' -- keep going
    else return constraints' -- stop here

minimiseOnce ::
  (GaloisField n, Bounded n, Integral n) =>
  -- | Initial constraint set
  Set (Constraint n) ->
  -- | Resulting simplified constraint set
  OptiM n (Set (Constraint n))
minimiseOnce = goOverConstraints Set.empty
  -- --
  -- -- constraints' <- goOverConstraints Set.empty constraints
  -- -- -- substitute roots/constants in constraints
  -- -- substituted <- mapM substConstraint $ Set.toList constraints'
  -- -- -- keep only constraints that is not tautologous
  -- -- removedTautology <- filterM (fmap not . isTautology) substituted
  -- return $ Set.fromList removedTautology

--
goOverConstraints ::
  (GaloisField n, Bounded n, Integral n) =>
  Set (Constraint n) ->
  Set (Constraint n) ->
  OptiM n (Set (Constraint n))
goOverConstraints accum constraints = case Set.minView constraints of
  Nothing -> return accum -- no more
  Just (picked, constraints') -> do
    -- pick the "smallest" constraint
    -- and substitute roots/constants in constraints
    substituted <- substConstraint picked
    -- if the constraint is tautologous, remove it
    tautologous <-  isTautology substituted

    if tautologous
      then goOverConstraints accum constraints'
      else do
        learn substituted
        goOverConstraints (Set.insert substituted accum) constraints'

-- traceShow (show picked <> " => " <> show substituted) $

--------------------------------------------------------------------------------

-- | Normalize constraints by substituting roots/constants
-- for the variables that appear in the constraint. Note that, when
-- normalizing a multiplicative constraint, it may be necessary to
-- convert it into an additive constraint.
substConstraint :: (GaloisField n, Bounded n, Integral n) => Constraint n -> OptiM n (Constraint n)
substConstraint !constraint = case constraint of
  CAdd constant coeffMap -> do
    (constant', coeffMap') <- foldM go (constant, mempty) (CoeffMap.toList coeffMap)
    return $ CAdd constant' (CoeffMap.fromList coeffMap')
    where
      go :: GaloisField n => (n, [(Var, n)]) -> (Var, n) -> OptiM n (n, [(Var, n)])
      go (accConstant, accMapping) (var, coeff) = do
        -- see if we can substitute a variable with some constant
        result <- lookupVar var
        case result of
          Root root -> do
            -- it's okay if we cannot substitute a variable with some constant
            -- we can still replace the variable with its root
            return (accConstant, (root, coeff) : accMapping)
          Value val -> do
            let val' = val * coeff
            -- if `value * coeff` is 0 then we should remove it
            if val' == 0
              then return (accConstant, accMapping)
              else return (accConstant + val', accMapping)
  CMul (c, x) (d, y) !ez -> do
    bx <- lookupVar x
    by <- lookupVar y
    bz <- lookupTerm ez
    case (bx, by, bz) of
      (Root rx, Root ry, Left (e, rz)) ->
        return
          $! CMul (c, rx) (d, ry) (e, Just rz)
      (Root rx, Root ry, Right e) ->
        return
          $! CMul (c, rx) (d, ry) (e, Nothing)
      (Root rx, Value d0, Left (e, rz)) ->
        return
          $! cadd 0 [(rx, c * d * d0), (rz, - e)]
      (Root rx, Value d0, Right e) ->
        return
          $! cadd (- e) [(rx, c * d * d0)]
      (Value c0, Root ry, Left (e, rz)) ->
        return
          $! cadd 0 [(ry, c0 * c * d), (rz, - e)]
      (Value c0, Root ry, Right e) ->
        return
          $! cadd (- e) [(ry, c0 * c * d)]
      (Value c0, Value d0, Left (e, rz)) ->
        return
          $! cadd (c * c0 * d * d0) [(rz, - e)]
      (Value c0, Value d0, Right e) ->
        return
          $! cadd (c * c0 * d * d0 - e) []
    where
      lookupTerm (e, Nothing) = return (Right e)
      lookupTerm (e, Just z) = do
        result <- lookupVar z
        case result of
          Root rz -> return (Left (e, rz))
          Value e0 -> return (Right (e * e0))
  CNQZ _ _ -> return constraint

-- | Is a constriant of `0 = 0` ?
isTautology :: GaloisField n => Constraint n -> OptiM n Bool
isTautology constraint = case constraint of
  CAdd _ coeffMap -> return $ CoeffMap.null coeffMap
  CMul {} -> return False
  CNQZ var m -> do
    result <- lookupVar var
    case result of
      Root _ -> return False
      Value 0 -> do
        bindVar m 0
        return True
      Value n -> do
        bindVar m (recip n)
        return True

-- | Learn bindings and variable equalities from a constraint
learn :: GaloisField n => Constraint n -> OptiM n ()
learn (CAdd a xs) = case CoeffMap.toList xs of
  [(x, c)] ->
    if c == 0
      then return ()
      else bindVar x (- a / c)
  [(x, c), (y, d)] -> when (a == 0 && c == - d) $ unifyVars x y
  _ -> return ()
learn _ = return ()

-- NOTE: We handle pinned variables 'var' as follows:
--  (1) Look up the term associated with
--      the pinned variable, if any (call it 't').
--  (2) If there is no such term (other than 'x' itself),
--      do nothing (clauses containing the pinned
--      variable must still contain the pinned variable).
--  (3) Otherwise, introduce a new equation 'x = t'.
handlePinnedVars :: GaloisField n => [Var] -> OptiM n [Constraint n]
handlePinnedVars pinnedVars = do
  pinnedTerms <- forM pinnedVars $ \var -> do
    result <- lookupVar var
    return (var, result)

  let isNotRoot (var, reuslt) = Root var /= reuslt
  let pinnedEquations =
        map
          ( \(var, result) -> case result of
              Root root -> cadd 0 [(var, 1), (root, -1)] -- var == root
              Value c -> cadd (- c) [(var, 1)] -- var == c
          )
          $ filter isNotRoot pinnedTerms
  return pinnedEquations

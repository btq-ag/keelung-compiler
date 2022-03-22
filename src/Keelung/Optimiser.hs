--------------------------------------------------------------------------------
--  Constraint Set Minimization
--------------------------------------------------------------------------------
{-# LANGUAGE BangPatterns #-}

module Keelung.Optimiser where

import Control.Monad
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set
import Keelung.Constraint
import Keelung.Constraint.CoeffMap (CoeffMap (..))
import qualified Keelung.Constraint.CoeffMap as CoeffMap
import Keelung.Optimiser.Monad
import Keelung.Syntax.Common

--------------------------------------------------------------------------------

-- | Smart constructor for the CAdd constraint
cadd :: GaloisField n => n -> [(Var, n)] -> Constraint n
cadd !c !xs = CAdd c (CoeffMap.fromList xs)

-- | Normalize constraints by substituting roots/constants
-- for the variables that appear in the constraint. Note that, when
-- normalizing a multiplicative constraint, it may be necessary to
-- convert it into an additive constraint.
substConstraint :: GaloisField n => Constraint n -> OptiM n (Constraint n)
substConstraint !constraint = case constraint of
  CAdd constant coeffMap -> do
    (constant', coeffMap') <- foldM go (constant, mempty) (CoeffMap.toList coeffMap)
    return $ CAdd constant' (CoeffMap coeffMap')
    where
      go :: GaloisField n => (n, IntMap n) -> (Var, n) -> OptiM n (n, IntMap n)
      go (accConstant, accMapping) (var, coeff) = do
        -- see if we can substitute a variable with some constant
        result <- lookupVar var
        case result of
          Left _ -> do
            -- it's okay if we cannot substitute a variable with some constant
            -- we can still replace the variable with its root
            var' <- rootOfVar var
            return (accConstant, IntMap.insert var' coeff accMapping)
          Right val -> do
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
      (Left rx, Left ry, Left (e, rz)) ->
        return
          $! CMul (c, rx) (d, ry) (e, Just rz)
      (Left rx, Left ry, Right e) ->
        return
          $! CMul (c, rx) (d, ry) (e, Nothing)
      (Left rx, Right d0, Left (e, rz)) ->
        return
          $! cadd 0 [(rx, c * d * d0), (rz, - e)]
      (Left rx, Right d0, Right e) ->
        return
          $! cadd (- e) [(rx, c * d * d0)]
      (Right c0, Left ry, Left (e, rz)) ->
        return
          $! cadd 0 [(ry, c0 * c * d), (rz, - e)]
      (Right c0, Left ry, Right e) ->
        return
          $! cadd (- e) [(ry, c0 * c * d)]
      (Right c0, Right d0, Left (e, rz)) ->
        return
          $! cadd (c * c0 * d * d0) [(rz, - e)]
      (Right c0, Right d0, Right e) ->
        return
          $! cadd (c * c0 * d * d0 - e) []
    where
      lookupTerm (e, Nothing) = return (Right e)
      lookupTerm (e, Just z) = do
        result <- lookupVar z
        case result of
          Left rz -> return (Left (e, rz))
          Right e0 -> return (Right (e * e0))

-- | Is a constriant of `0 = 0` ?
isTautology :: GaloisField n => Constraint n -> Bool
isTautology constraint = case constraint of
  CAdd _ coeffMap -> CoeffMap.null coeffMap
  CMul {} -> False

-- | Learn bindings and variable equalities from a constraint
learn :: GaloisField n => Constraint n -> OptiM n ()
learn (CAdd a xs) = case CoeffMap.toList xs of
  [(x, c)] ->
    if c == 0
      then return ()
      else bindVar x (- a / c)
  [(x, c), (y, d)] -> when ((a == 0) && (c == - d)) $ unifyVars x y
  _ -> return ()
learn _ = return ()

simplifyConstrantSystem :: GaloisField n => Witness n -> ConstraintSystem n -> (Witness n, ConstraintSystem n)
simplifyConstrantSystem env cs =
  -- NOTE: Pinned vars include:
  --   - input vars
  --   - output vars
  -- Pinned vars are never optimized away.
  let pinnedVars = IntSet.toList $ csInputVars cs <> csOutputVars cs
   in runOptiM env $ do
        constraints <- simplifyConstraintSet pinnedVars (csConstraints cs)
        -- NOTE: In the next line, it's OK that 'pinnedVars'
        -- may overlap with 'constraintVars cs'.
        -- 'assignmentOfVars' might do a bit of duplicate
        -- work (to look up the same key more than once).
        assignments <- assignmentOfVars $ pinnedVars ++ IntSet.toList (varsInConstraints (csConstraints cs))
        return (assignments, cs {csConstraints = constraints})

simplifyConstraintSet ::
  GaloisField n =>
  [Var] ->
  Set (Constraint n) ->
  OptiM n (Set (Constraint n))
simplifyConstraintSet pinnedVars constraints =
  do
    simplified <- simplifyManyTimes constraints
    -- substitute roots/constants in constraints
    substituted <- mapM substConstraint $ Set.toList simplified
    -- keep only constraints that is not tautologous
    let removedTautology = filter (not . isTautology) substituted

    pinned <- handlePinnedVars pinnedVars
    return $ Set.fromList (pinned ++ removedTautology)

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
  let pinnedEquations =
        map
          ( \(var, result) -> case result of
              Left root -> cadd 0 [(var, 1), (root, -1)] -- var == root
              Right c -> cadd (- c) [(var, 1)] -- var == c
          )
          $ filter (\(var, reuslt) -> Left var /= reuslt) pinnedTerms
  return pinnedEquations

simplifyManyTimes ::
  GaloisField n =>
  -- | Initial constraint set
  Set (Constraint n) ->
  -- | Resulting simplified constraint set
  OptiM n (Set (Constraint n))
simplifyManyTimes constraints = do
  constraints' <- simplifyOnce constraints
  let hasShrunk = Set.size constraints' < Set.size constraints

  if hasShrunk
    then simplifyManyTimes constraints'
    else
      if Set.null (Set.difference constraints constraints')
        then return constraints'
        else simplifyManyTimes constraints'

-- TODO: see if the steps after `goOverConstraints` is necessary
simplifyOnce ::
  GaloisField n =>
  -- | Initial constraint set
  Set (Constraint n) ->
  -- | Resulting simplified constraint set
  OptiM n (Set (Constraint n))
simplifyOnce constraints = do
  --
  constraints' <- goOverConstraints Set.empty constraints
  -- substitute roots/constants in constraints
  substituted <- mapM substConstraint $ Set.toList constraints'
  -- keep only constraints that is not tautologous
  return $ Set.fromList $ filter (not . isTautology) substituted

goOverConstraints :: GaloisField n => Set (Constraint n) -> Set (Constraint n) -> OptiM n (Set (Constraint n))
goOverConstraints accum constraints = case Set.minView constraints of
  Nothing -> return accum -- no more
  Just (picked, constraints') -> do
    -- pick the "smallest" constraint
    substituted <- substConstraint picked
    if isTautology substituted
      then goOverConstraints accum constraints'
      else do
        learn substituted
        goOverConstraints (Set.insert substituted accum) constraints'
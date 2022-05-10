{-# LANGUAGE BangPatterns #-}

module Keelung.Optimise.MinimiseConstraints (run, substConstraint) where

import Control.Monad
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import qualified Data.Set as Set
import Keelung.Constraint (Constraint (..), cadd)
import Keelung.Constraint.Vector (Vector)
import qualified Keelung.Constraint.Vector as Vector
import Keelung.Optimise.Monad
import Keelung.Syntax.Common (Var)

run ::
  (GaloisField n, Bounded n, Integral n) =>
  [Var] ->
  Set (Constraint n) ->
  OptiM n (Set (Constraint n))
run pinnedVars constraints = do
  minimised <- minimiseManyTimes constraints
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
    tautologous <- isTautology substituted

    if tautologous
      then goOverConstraints accum constraints'
      else do
        learn substituted
        goOverConstraints (Set.insert substituted accum) constraints'

-- traceShow (show picked <> " => " <> show substituted) $

--------------------------------------------------------------------------------

-- | Normalize a vector by substituting roots/constants
-- for the variables that appear in the vector.
substVector :: (GaloisField n, Bounded n, Integral n) => Vector n -> OptiM n (Vector n)
substVector vector = do
  let coeffs = IntMap.toList (Vector.coeffs vector)
  (constant', coeffs') <- foldM go (Vector.constant vector, mempty) coeffs
  return $ Vector.build constant' coeffs'
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

-- | Normalize constraints by substituting roots/constants
-- for the variables that appear in the constraint. Note that, when
-- normalizing a multiplicative constraint, it may be necessary to
-- convert it into an additive constraint.
substConstraint :: (GaloisField n, Bounded n, Integral n) => Constraint n -> OptiM n (Constraint n)
substConstraint !constraint = case constraint of
  CAdd vector -> CAdd <$> substVector vector
  -- CMul (c, x) (d, y) !ez -> do
  --   bx <- lookupVar x
  --   by <- lookupVar y
  --   bz <- lookupTerm ez
  --   case (bx, by, bz) of
  --     (Root rx, Root ry, Left (e, rz)) ->
  --       -- ax * by = cz
  --       return
  --         $! CMul (c, rx) (d, ry) (e, Just rz)
  --     (Root rx, Root ry, Right e) ->
  --       -- ax * by = c
  --       return
  --         $! CMul (c, rx) (d, ry) (e, Nothing)
  --     (Root rx, Value d0, Left (e, rz)) ->
  --       -- ax * b = cz => ax * b - cz = 0
  --       return
  --         $! cadd 0 [(rx, c * d * d0), (rz, - e)]
  --     (Root rx, Value d0, Right e) ->
  --       -- ax * b = c => ax * b - c = 0
  --       return
  --         $! cadd (- e) [(rx, c * d * d0)]
  --     (Value c0, Root ry, Left (e, rz)) ->
  --       -- a * bx = cz => a * bx - cz = 0
  --       return
  --         $! cadd 0 [(ry, c0 * c * d), (rz, - e)]
  --     (Value c0, Root ry, Right e) ->
  --       -- a * bx = c => a * bx - c = 0
  --       return
  --         $! cadd (- e) [(ry, c0 * c * d)]
  --     (Value c0, Value d0, Left (e, rz)) ->
  --       -- a * b = cz => a * b - cz = 0
  --       return
  --         $! cadd (c * c0 * d * d0) [(rz, - e)]
  --     (Value c0, Value d0, Right e) ->
  --       -- a * b = c => a * b - c = 0
  --       return
  --         $! cadd (c * c0 * d * d0 - e) []
  --   where
  --     lookupTerm (e, Nothing) = return (Right e)
  --     lookupTerm (e, Just z) = do
  --       result <- lookupVar z
  --       case result of
  --         Root rz -> return (Left (e, rz))
  --         Value e0 -> return (Right (e * e0))
  CMul2 aV bV cV -> do
    aV' <- substVector aV
    bV' <- substVector bV
    cV' <- substVector cV

    -- if either aV' or bV' is constant
    -- we can convert this multiplicative constraint into an additive one
    return $ case (Vector.view aV', Vector.view bV', Vector.view cV') of
      -- a * b = c => a * b - c = 0
      (Left a, Left b, Left c) -> CAdd $ Vector.build' (a * b - c) mempty
      -- a * b = c + cx => a * b - c - cx = 0
      (Left a, Left b, Right (c, cX)) ->
        CAdd $ Vector.build' (a * b - c) cX
      -- a * (b + bx) = c => a * bx + a * b - c = 0
      (Left a, Right (b, bX), Left c) -> do
        let constant = a * b - c
        let coeffs = fmap (a *) bX
        CAdd $ Vector.build' constant coeffs
      -- a * (b + bx) = c + cx => a * bx - cx + a * b - c = 0
      (Left a, Right (b, bX), Right (c, cX)) -> do
        let constant = a * b - c
        let coeffs = Vector.mergeCoeffs (fmap (a *) bX) (fmap negate cX)
        CAdd $ Vector.build' constant coeffs
      -- (a + ax) * b = c => ax * b + a * b - c= 0
      (Right (a, aX), Left b, Left c) -> do
        let constant = a * b - c
        let coeffs = fmap (* b) aX
        CAdd $ Vector.build' constant coeffs
      -- (a + ax) * b = c + cx => ax * b - cx + a * b - c = 0
      (Right (a, aX), Left b, Right (c, cX)) -> do
        let constant = a * b - c
        let coeffs = Vector.mergeCoeffs (fmap (* b) aX) (fmap negate cX)
        CAdd $ Vector.build' constant coeffs
      -- (a + ax) * (b + bx) = c
      -- (a + ax) * (b + bx) = c + cx
      (Right _, Right _, _) -> do
        CMul2 aV' bV' cV'
  CNQZ _ _ -> return constraint

-- | Is a constriant of `0 = 0` ?
isTautology :: GaloisField n => Constraint n -> OptiM n Bool
isTautology constraint = case constraint of
  CAdd xs -> return $ Vector.isConstant xs
  -- CMul {} -> return False
  CMul2 {} -> return False -- TODO: revise this 
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
learn (CAdd xs) = case IntMap.toList (Vector.coeffs xs) of
  [(x, c)] ->
    if c == 0
      then return ()
      else bindVar x (- Vector.constant xs / c)
  [(x, c), (y, d)] -> when (Vector.constant xs == 0 && c == - d) $ unifyVars x y
  _ -> return ()
-- learn (CAdd a xs) = case CoeffMap.toList xs of
--   [(x, c)] ->
--     if c == 0
--       then return ()
--       else bindVar x (- a / c)
--   [(x, c), (y, d)] -> when (a == 0 && c == - d) $ unifyVars x y
--   _ -> return ()
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

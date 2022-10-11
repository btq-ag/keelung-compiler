{-# LANGUAGE BangPatterns #-}

module Keelung.Compiler.Optimize.MinimizeConstraints (run, substConstraint) where

import Control.Monad
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import qualified Data.Set as Set
import Keelung.Compiler.Constraint (Constraint (..), cadd)
import Keelung.Compiler.Optimize.Monad
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Types (Var)

run ::
  (GaloisField n, Integral n) =>
  [Var] ->
  Set (Constraint n) ->
  OptiM n (Set (Constraint n))
run pinnedVars constraints = do
  minimised <- minimiseManyTimes constraints
  pinned <- handlePinnedVars pinnedVars
  return (Set.fromList pinned <> minimised)

minimiseManyTimes ::
  (GaloisField n, Integral n) =>
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
  (GaloisField n, Integral n) =>
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
  (GaloisField n, Integral n) =>
  Set (Constraint n) ->
  Set (Constraint n) ->
  OptiM n (Set (Constraint n))
goOverConstraints accum constraints = case Set.minView constraints of
  Nothing -> return accum -- no more
  Just (picked, constraints') -> do
    -- pick the "smallest" constraint
    -- and substitute roots/constants in constraints
    substitutionResult <- substConstraint picked

    case substitutionResult of
      -- constaint got optimized away
      Nothing -> goOverConstraints accum constraints'
      Just substituted -> do
        -- if the constraint is tautologous, remove it
        tautologous <- isTautology substituted

        if tautologous
          then goOverConstraints accum constraints'
          else do
            learn substituted
            goOverConstraints (Set.insert substituted accum) constraints'

--------------------------------------------------------------------------------

-- | Normalize a polynomial by substituting roots/constants
-- for the variables that appear in the polynomial.
substPoly :: GaloisField n => Poly n -> OptiM n (Either n (Poly n))
substPoly poly = do
  let coeffs = IntMap.toList (Poly.coeffs poly)
  (constant', coeffs') <- foldM go (Poly.constant poly, mempty) coeffs

  return $ Poly.buildEither constant' coeffs'
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
substConstraint :: GaloisField n => Constraint n -> OptiM n (Maybe (Constraint n))
substConstraint !constraint = case constraint of
  CAdd poly -> do
    result <- substPoly poly
    case result of
      Left _ -> return Nothing
      Right poly' -> return $ Just $ CAdd poly'
  CMul aV bV cV -> do
    aV' <- substPoly aV
    bV' <- substPoly bV
    cV' <- join <$> mapM substPoly cV

    -- if either aV' or bV' is constant
    -- we can convert this multiplicative constraint into an additive one
    return $ case (Poly.view <$> aV', Poly.view <$> bV', Poly.view <$> cV') of
      -- a * b = c => a * b - c = 0
      (Left _, Left _, Left _) -> Nothing
      -- a * b = c + cx => a * b - c - cx = 0
      (Left a, Left b, Right (c, cX)) ->
        CAdd <$> Poly.buildMaybe (a * b - c) cX
      -- a * (b + bx) = c => a * bx + a * b - c = 0
      (Left a, Right (b, bX), Left c) -> do
        let constant = a * b - c
        let coeffs = fmap (a *) bX
        CAdd <$> Poly.buildMaybe constant coeffs
      -- a * (b + bx) = c + cx => a * bx - cx + a * b - c = 0
      (Left a, Right (b, bX), Right (c, cX)) -> do
        let constant = a * b - c
        let coeffs = Poly.mergeCoeffs (fmap (a *) bX) (fmap negate cX)
        CAdd <$> Poly.buildMaybe constant coeffs
      -- (a + ax) * b = c => ax * b + a * b - c= 0
      (Right (a, aX), Left b, Left c) -> do
        let constant = a * b - c
        let coeffs = fmap (* b) aX
        CAdd <$> Poly.buildMaybe constant coeffs
      -- (a + ax) * b = c + cx => ax * b - cx + a * b - c = 0
      (Right (a, aX), Left b, Right (c, cX)) -> do
        let constant = a * b - c
        let coeffs = Poly.mergeCoeffs (fmap (* b) aX) (fmap negate cX)
        CAdd <$> Poly.buildMaybe constant coeffs
      -- (a + ax) * (b + bx) = c
      -- (a + ax) * (b + bx) = c + cx
      (Right (a, aX), Right (b, bX), Left c) -> do
        CMul <$> Poly.buildMaybe a aX <*> Poly.buildMaybe b bX
          <*> pure (Left c)
      (Right (a, aX), Right (b, bX), Right (c, cX)) -> do
        CMul <$> Poly.buildMaybe a aX <*> Poly.buildMaybe b bX
          <*> pure (Poly.buildEither c (IntMap.toList cX))
  CNQZ {} -> return $ Just constraint
  CXor x y z -> do
    x' <- lookupVar x
    y' <- lookupVar y
    z' <- lookupVar z
    case (x', y', z') of
      (Value _, Value _, Value _) -> return Nothing
      (Value 0, Value 0, Root c) -> bindVar c 0 >> return Nothing
      (Value 0, Value _, Root c) -> bindVar c 1 >> return Nothing
      (Value _, Value 0, Root c) -> bindVar c 1 >> return Nothing
      (Value _, Value _, Root c) -> bindVar c 0 >> return Nothing
      (Value 0, Root b, Value 0) -> bindVar b 0 >> return Nothing
      (Value 0, Root b, Value _) -> bindVar b 1 >> return Nothing
      (Value _, Root b, Value 0) -> bindVar b 1 >> return Nothing
      (Value _, Root b, Value _) -> bindVar b 0 >> return Nothing
      (Root a, Value 0, Value 0) -> bindVar a 0 >> return Nothing
      (Root a, Value 0, Value _) -> bindVar a 1 >> return Nothing
      (Root a, Value _, Value 0) -> bindVar a 1 >> return Nothing
      (Root a, Value _, Value _) -> bindVar a 0 >> return Nothing
      (Value 0, Root b, Root c) -> unifyVars b c >> return Nothing
      (Value _, Root b, Root c) -> return $ Just $ CXor x b c -- TODO: learn about this case
      (Root a, Value 0, Root c) -> unifyVars a c >> return Nothing
      (Root a, Value _, Root c) -> return $ Just $ CXor a y c -- TODO: learn about this case
      (Root a, Root b, Value 0) -> unifyVars a b >> return Nothing
      (Root a, Root b, Value _) -> return $ Just $ CXor a b z -- TODO: learn about this case
      (Root a, Root b, Root c) -> return $ Just $ CXor a b c
  COr x y z -> do
    x' <- lookupVar x
    y' <- lookupVar y
    z' <- lookupVar z
    case (x', y', z') of
      (Value _, Value _, Value _) -> return Nothing
      (Value 0, Value 0, Root c) -> bindVar c 0 >> return Nothing
      (Value 0, Value _, Root c) -> bindVar c 1 >> return Nothing
      (Value _, Value 0, Root c) -> bindVar c 1 >> return Nothing
      (Value _, Value _, Root c) -> bindVar c 1 >> return Nothing
      (Value 0, Root b, Value 0) -> bindVar b 0 >> return Nothing
      (Value 0, Root b, Value _) -> bindVar b 1 >> return Nothing
      (Value _, Root _, Value _) -> return Nothing
      (Root a, Value 0, Value 0) -> bindVar a 0 >> return Nothing
      (Root a, Value 0, Value _) -> bindVar a 1 >> return Nothing
      (Root _, Value _, Value 0) -> return Nothing
      (Root _, Value _, Value _) -> return Nothing
      (Value 0, Root b, Root c) -> unifyVars b c >> return Nothing
      (Value _, Root _, Root c) -> bindVar c 1 >> return Nothing
      (Root a, Value 0, Root c) -> unifyVars a c >> return Nothing
      (Root _, Value _, Root c) -> bindVar c 1 >> return Nothing
      (Root a, Root b, Value 0) -> bindVar a 0 >> bindVar b 0 >> return Nothing
      (Root a, Root b, Value _) -> return $ Just $ COr a b z
      (Root a, Root b, Root c) -> return $ Just $ COr a b c

-- | Is a constriant of `0 = 0` or "x * n = nx" or "m * n = mn" ?
isTautology :: GaloisField n => Constraint n -> OptiM n Bool
isTautology constraint = case constraint of
  CAdd _ -> return False
  CMul {} -> return False
  -- CMul aV bV cV -> case (Poly.view aV, Poly.view bV, Poly.view cV) of
  --   (Left a, Right (b, bX), Right (c, cX)) ->
  --     return $
  --       a * b == c && fmap (a *) bX == cX
  --   (Right (a, aX), Left b, Right (c, cX)) ->
  --     return $
  --       a * b == c && fmap (* b) aX == cX
  --   (Left a, Left b, Left c) ->
  --     return $
  --       a * b == c
  --   _ -> return False
  CNQZ x y m -> do
    x' <- lookupVar x
    case x' of
      Root _ -> return False
      Value xVal -> do
        y' <- lookupVar y
        case y' of
          Root _ -> return False
          Value yVal -> do
            let diff = xVal - yVal
            if diff == 0
              then do
                bindVar m 0
                return True
              else do
                bindVar m (recip diff)
                return True
  CXor x y z -> do
    x' <- lookupVar x
    case x' of
      Root _ -> return False
      Value x'' -> do
        y' <- lookupVar y
        case y' of
          Root _ -> return False
          Value y'' -> do
            z' <- lookupVar z
            case z' of
              Root _ -> return False
              Value z'' ->
                return $ x'' + y'' - 2 * (x'' * y'') == z''
  COr x y z -> do
    x' <- lookupVar x
    case x' of
      Root _ -> return False
      Value x'' -> do
        y' <- lookupVar y
        case y' of
          Root _ -> return False
          Value y'' -> do
            z' <- lookupVar z
            case z' of
              Root _ -> return False
              Value z'' ->
                return $ x'' + y'' - (x'' * y'') == z''

-- | Learn bindings and variable equalities from a constraint
learn :: (GaloisField n, Integral n) => Constraint n -> OptiM n ()
learn (CAdd xs) = case IntMap.toList (Poly.coeffs xs) of
  [(x, c)] ->
    if c == 0
      then return ()
      else bindVar x (- Poly.constant xs / c)
  [(x, c), (y, d)] -> when (Poly.constant xs == 0 && c == - d) $ unifyVars x y
  _ -> return ()
-- learn (CAdd a xs) = case CoeffMap.toList xs of
--   [(x, c)] ->
--     if c == 0
--       then return ()
--       else bindVar x (- a / c)
--   [(x, c), (y, d)] -> when (a == 0 && c == - d) $ unifyVars x y
--   _ -> return ()
learn (CXor x y z)
  | x == z = bindVar y 0 -- x ⊕ y = x => y = 0
  | y == z = bindVar x 0 -- x ⊕ y = y => x = 0
  | x == y = bindVar z 0 -- x ⊕ x = z => z = 0
  | otherwise = return ()
learn COr {} = return ()
learn _ = return ()

-- NOTE: We handle pinned variables 'var' as follows:
--  (1) Look up the term associated with
--      the pinned variable, if any (call it 't').
--  (2) If there is no such term (other than 'x' itself),
--      do nothing (constraints containing the pinned
--      variable must still contain the pinned variable).
--  (3) Otherwise, introduce a new equation 'x = t'.
handlePinnedVars :: GaloisField n => [Var] -> OptiM n [Constraint n]
handlePinnedVars pinnedVars = do
  pinnedTerms <- forM pinnedVars $ \var -> do
    result <- lookupVar var
    return (var, result)

  let isNotRoot (var, reuslt) = Root var /= reuslt
  let pinnedEquations =
        concatMap
          ( \(var, result) -> case result of
              Root root -> cadd 0 [(var, 1), (root, -1)] -- var == root
              Value c -> cadd (- c) [(var, 1)] -- var == c
          )
          (filter isNotRoot pinnedTerms)
  return pinnedEquations

{-# LANGUAGE BangPatterns #-}

module Keelung.Compiler.Optimize.MinimizeRelocatedConstraints (run, substConstraint) where

import Control.Monad
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import qualified Data.Set as Set
import Keelung.Compiler.Relocated (Constraint (..), cadd)
import Keelung.Compiler.Optimize.Monad
import Keelung.Compiler.Syntax.FieldBits (toBits)
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Constraint.R1CS (CNEQ (..))
import Keelung.Syntax.BinRep (BinRep (BinRep))
import Keelung.Syntax.Counters
import Keelung.Types (Var)

run ::
  (GaloisField n, Integral n) =>
  Counters ->
  [Var] ->
  Set (Constraint n) ->
  OptiM n (Set (Constraint n))
run counters pinnedVars constraints = do
  minimised <- minimiseManyTimes (constraints, getBinReps counters)
  pinned <- handlePinnedVars pinnedVars
  return (Set.fromList pinned <> minimised)

minimiseManyTimes ::
  (GaloisField n, Integral n) =>
  -- | Initial constraint set
  (Set (Constraint n), [BinRep]) ->
  -- | Resulting simplified constraint set
  OptiM n (Set (Constraint n))
minimiseManyTimes (constraints, binReps) = do
  constraints' <- minimiseConstraintsOnce constraints
  -- see if the constraints have changed
  let constraintHadChanged =
        (Set.size constraints' < Set.size constraints)
          || not (Set.null (Set.difference constraints constraints'))
  -- keep minimising if the constraints have shrunk or changed
  if constraintHadChanged
    then minimiseManyTimes (constraints', binReps) -- keep going
    else do
      binReps' <- goOverBinReps binReps
      let binRepsHadShrinked = length binReps' < length binReps
      if binRepsHadShrinked
        then minimiseManyTimes (constraints', binReps') -- keep going
        else return constraints' -- there's nothing we can do, stop here

minimiseConstraintsOnce ::
  (GaloisField n, Integral n) =>
  -- | Initial constraint set
  Set (Constraint n) ->
  -- | Resulting simplified constraint set
  OptiM n (Set (Constraint n))
minimiseConstraintsOnce = goOverConstraints Set.empty

-- | Go over BinReps, fill in the bit variables if we know the value, and throw them away
goOverBinReps :: (GaloisField n, Integral n) => [BinRep] -> OptiM n [BinRep]
goOverBinReps = filterM substBinRep

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

-- | Returns `False` if we have learned something about this BinRep
substBinRep :: (Integral n, GaloisField n) => BinRep -> OptiM n Bool
substBinRep (BinRep var w bits) = do
  -- although a value is isomorphic to its binary representation
  -- we are only substituting the bits in the binary representation
  result <- lookupVar var
  case result of
    Root _ -> do
      -- dunno the value of "var", see if we can go the other way and restore the value of "var" from its bits
      varValue <-
        foldM
          ( \acc bitVar -> case acc of
              Nothing -> return Nothing
              Just accVal -> do
                bitValue <- lookupVar bitVar
                case bitValue of
                  Root _ -> return Nothing
                  Value bit -> return (Just (accVal * 2 + bit))
          )
          (Just 0)
          [bits + w - 1, bits + w - 2 .. bits]
      case varValue of
        Nothing -> return True
        Just varValue' -> do
          bindVar var varValue'
          return False
    Value n -> do
      forM_ (zip [bits .. bits + w - 1] (toBits n)) $ \(index, bit) -> do
        bindVar index bit
      return False

-- | Normalize constraints by substituting roots/constants
-- for the variables that appear in the constraint. Note that, when
-- normalizing a multiplicative constraint, it may be necessary to
-- convert it into an additive constraint.
substConstraint :: (GaloisField n, Integral n) => Constraint n -> OptiM n (Maybe (Constraint n))
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
        CAdd <$> Poly.buildMaybe (a * b - c) (fmap negate cX)
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
      -- (a + ax) * b = c => ax * b + a * b - c = 0
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
  CNEq (CNEQ x y m) -> do
    x' <- case x of
      Left var -> lookupVar var
      Right val -> return $ Value val
    y' <- case y of
      Left var -> lookupVar var
      Right val -> return $ Value val
    case (x', y') of
      (Root xR, Root yR) -> return $ Just $ CNEq $ CNEQ (Left xR) (Left yR) m
      (Value xV, Root yR) -> return $ Just $ CNEq $ CNEQ (Right xV) (Left yR) m
      (Root xR, Value yV) -> return $ Just $ CNEq $ CNEQ (Left xR) (Right yV) m
      (Value xV, Value yV) -> do
        let diff = xV - yV
        if diff == 0
          then do
            bindVar m 0
            return Nothing
          else do
            bindVar m (recip diff)
            return Nothing

-- | Is a constriant of `0 = 0` or "x * n = nx" or "m * n = mn" ?
isTautology :: GaloisField n => Constraint n -> OptiM n Bool
isTautology constraint = case constraint of
  CAdd _ -> return False
  CMul {} -> return False
  -- we assume that the variables in CNEQ has all been substituted with values when possible
  -- so that we can just check if the values are equal
  CNEq {} -> return False

-- | Learn bindings and variable equalities from a constraint
learn :: (GaloisField n, Integral n) => Constraint n -> OptiM n ()
learn (CAdd xs) = case IntMap.toList (Poly.coeffs xs) of
  [(x, c)] ->
    if c == 0
      then return ()
      else bindVar x (-Poly.constant xs / c)
  [(x, c), (y, d)] -> when (Poly.constant xs == 0 && c == -d) $ unifyVars x y
  _ -> return ()
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
              Value c -> cadd (-c) [(var, 1)] -- var == c
          )
          (filter isNotRoot pinnedTerms)
  return pinnedEquations

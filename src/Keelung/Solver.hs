-- | Witness solver/generator for R1CS
module Keelung.Solver
  ( run,
    debug,
    Error (..),
    Log (..),
    LogReport (..),
    module Keelung.Solver.BinRep,
  )
where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Bits qualified
import Data.Foldable (toList)
import Data.IntMap.Strict qualified as IntMap
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Keelung hiding (witness)
import Keelung.Compiler.Options
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Constraint.R1C
import Keelung.Constraint.R1CS
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Solver.BinRep
import Keelung.Solver.Monad
import Keelung.Syntax.Counters

-- | Execute the R1CS solver
run :: (GaloisField n, Integral n) => Options -> R1CS n -> Inputs n -> Either (Error n) (Vector n, Vector n)
run options r1cs inputs = fst (run' False options r1cs inputs)

-- | Like `run`, but with debug logs
debug :: (GaloisField n, Integral n) => R1CS n -> Inputs n -> (Either (Error n) (Vector n, Vector n), Maybe (LogReport n))
debug = run' True defaultOptions

-- | Returns (interpreted outputs, witnesses, log)s
run' :: (GaloisField n, Integral n) => Bool -> Options -> R1CS n -> Inputs n -> (Either (Error n) (Vector n, Vector n), Maybe (LogReport n))
run' debugMode _options r1cs inputs = do
  let booleanConstraintCategories = [(Output, ReadBool), (Output, ReadAllUInts), (PublicInput, ReadBool), (PublicInput, ReadAllUInts), (PrivateInput, ReadBool), (PrivateInput, ReadAllUInts), (Intermediate, ReadBool), (Intermediate, ReadAllUInts)]
  let boolVarRanges = getRanges (r1csCounters r1cs) booleanConstraintCategories
  case fromOrdinaryConstraints r1cs of
    Left err -> (Left err, Nothing)
    Right constraints -> do
      let (result, logs) = runM debugMode boolVarRanges (r1csField r1cs) inputs $ goThroughManyTimes constraints
      case result of
        Left (err, _) -> (Left err, Just logs)
        Right witness ->
          -- extract output values from the witness
          let outputRanges = getRanges (r1csCounters r1cs) [(Output, ReadField), (Output, ReadBool), (Output, ReadAllUInts)]
           in case IntMap.toList outputRanges of
                [(outputStart, outputLength)] -> (Right (Vector.slice outputStart outputLength witness, witness), Just logs)
                _ -> (Right (mempty, witness), Just logs)

-- | Return Constraints from a R1CS, which include:
--   1. ordinary constraints
--   2. Boolean input variable constraints
--   3. binary representation constraints
--   4. CNEQ constraints
fromOrdinaryConstraints :: (GaloisField n, Integral n) => R1CS n -> Either (Error n) (Seq (Constraint n))
fromOrdinaryConstraints (R1CS _ ordinaryConstraints counters eqZeros divMods clDivMods modInvs) = do
  constraints <- concat <$> mapM differentiate ordinaryConstraints
  return $
    Seq.fromList constraints
      <> Seq.fromList (map BooleanConstraint booleanInputVarConstraints)
      <> Seq.fromList (map EqZeroConstraint eqZeros)
      <> Seq.fromList (map DivModConstaint divMods)
      <> Seq.fromList (map CLDivModConstaint clDivMods)
      <> Seq.fromList (map ModInvConstraint modInvs)
  where
    booleanInputVarConstraints =
      let generateRange (start, end) = [start .. end - 1]
       in concatMap generateRange (IntMap.toList (getBooleanConstraintRanges counters))

    differentiate :: (GaloisField n, Integral n) => R1C n -> Either (Error n) [Constraint n]
    differentiate (R1C (Left a) (Left b) (Left c)) = if a * b == c then Right [] else Left (ConflictingValues "multplicative R1C with all constants")
    differentiate (R1C (Left a) (Left b) (Right c)) = Right [AddConstraint $ Poly.addConstant (-a * b) c]
    differentiate (R1C (Left a) (Right b) (Left c)) = case Poly.multiplyBy a b of
      Left constant ->
        if constant == c
          then Right []
          else Left (ConflictingValues "multplicative R1C with constant on the left")
      Right poly -> Right [AddConstraint $ Poly.addConstant (-c) poly]
    differentiate (R1C (Left a) (Right b) (Right c)) = case Poly.multiplyBy (-a) b of
      Left constant -> Right [AddConstraint $ Poly.addConstant constant c]
      Right poly -> case Poly.merge poly c of
        Left constant ->
          if constant == 0
            then Right []
            else Left (ConflictingValues "multplicative R1C with constant on the right")
        Right poly' -> Right [AddConstraint poly']
    differentiate (R1C (Right a) (Left b) (Left c)) = differentiate (R1C (Left b) (Right a) (Left c))
    differentiate (R1C (Right a) (Left b) (Right c)) = differentiate (R1C (Left b) (Right a) (Right c))
    differentiate (R1C (Right a) (Right b) c) = Right [MulConstraint a b c]

goThroughManyTimes :: (GaloisField n, Integral n) => Seq (Constraint n) -> M n ()
goThroughManyTimes constraints = do
  result <- goThroughOnce constraints
  case result of
    -- keep going
    Shrinked constraints' -> goThroughManyTimes constraints'
    -- done
    Eliminated -> return ()
    NothingToDo -> return ()
    -- stuck
    Stuck _ -> do
      context <- get
      throwError (StuckError context (toList constraints))

-- Go through a sequence of constraints
goThroughOnce :: (GaloisField n, Integral n) => Seq (Constraint n) -> M n (Result (Seq (Constraint n)))
goThroughOnce constraints = mconcat <$> mapM shrink (toList constraints)

lookupVar :: Var -> M n (Maybe n)
lookupVar var = gets (IntMap.lookup var)

-- | If all limbs are assigned values, then return the combined value of the limbs
lookupLimbs :: (GaloisField n, Integral n) => Limbs -> M n (Maybe U)
lookupLimbs limbs = do
  vals <- mapM lookupLimb limbs
  case sequence vals of
    Nothing -> return Nothing
    Just limbVals -> do
      -- all limbs are assigned values, concatenate them all!
      return $ Just $ mconcat limbVals
  where
    lookupLimb :: (GaloisField n, Integral n) => (Width, Either Var Integer) -> M n (Maybe U)
    lookupLimb (width, Left var) = do
      vals <- mapM lookupVar [var .. var + width - 1]
      case sequence vals of
        Nothing -> return Nothing
        Just bitVals -> do
          -- all bit variables are assigned values!
          return $ Just $ U.new width $ sum [toInteger bitVal * (2 ^ i) | (i, bitVal) <- zip [0 :: Int ..] bitVals]
    lookupLimb (width, Right val) = return (Just (U.new width val))

shrink :: (GaloisField n, Integral n) => Constraint n -> M n (Result (Seq (Constraint n)))
shrink (MulConstraint as bs cs) = do
  xs <- shrinkMul as bs cs >>= shrinkBinRep
  case xs of
    Shrinked xs' -> tryLog $ LogShrinkConstraint (MulConstraint as bs cs) xs'
    Stuck _ -> return ()
    Eliminated -> tryLog $ LogEliminateConstraint (MulConstraint as bs cs)
    NothingToDo -> return ()
  return $ fmap Seq.singleton xs
shrink (AddConstraint as) = do
  as' <- shrinkAdd as >>= shrinkBinRep
  return $ fmap Seq.singleton as'
shrink (BooleanConstraint var) = fmap (pure . BooleanConstraint) <$> shrinkBooleanConstraint var
shrink (EqZeroConstraint eqZero) = fmap (pure . EqZeroConstraint) <$> shrinkEqZero eqZero
shrink (DivModConstaint divModTuple) = fmap (pure . DivModConstaint) <$> shrinkDivMod False divModTuple
shrink (CLDivModConstaint divModTuple) = fmap (pure . CLDivModConstaint) <$> shrinkDivMod True divModTuple
shrink (ModInvConstraint modInvHint) = fmap (pure . ModInvConstraint) <$> shrinkModInv modInvHint

shrinkAdd :: (GaloisField n, Integral n) => Poly n -> M n (Result (Constraint n))
shrinkAdd xs = do
  bindings <- get
  case substAndView bindings xs of
    Constant c -> eliminateIfHold c 0
    Uninomial _ _ c (var, coeff) -> do
      -- c + coeff var = 0
      bindVar "add" var (-c / coeff)
      return Eliminated
    Polynomial changed xs' -> return $ shrinkedOrStuck [changed] $ AddConstraint xs'

shrinkMul :: (GaloisField n, Integral n) => Poly n -> Poly n -> Either n (Poly n) -> M n (Result (Constraint n))
shrinkMul as bs (Left c) = do
  bindings <- get
  case (substAndView bindings as, substAndView bindings bs) of
    (Constant a, Constant b) -> eliminateIfHold (a * b) c
    (Constant 0, Uninomial {}) -> eliminateIfHold 0 c -- 'c' should be 0
    (Constant a, Uninomial _ _ b (var, coeff)) -> do
      -- a * (b + coeff var) = c
      --    =>
      -- a * b + a * coeff * var = c
      --    =>
      -- a * coeff * var = c - a * b
      --    =>
      -- var = (c - a * b) / (coeff * a)
      bindVar "mul 1" var ((c - a * b) / (coeff * a))
      return Eliminated
    (Constant a, Polynomial _ bs') -> case Poly.multiplyBy a bs' of
      Left constant -> eliminateIfHold constant c
      Right poly -> return $ Shrinked $ AddConstraint $ Poly.addConstant (-c) poly
    (Uninomial {}, Constant 0) -> eliminateIfHold 0 c -- 'c' should be 0
    (Uninomial _ _ a (var, coeff), Constant b) -> do
      -- (a + coeff var) * b = c
      bindVar "mul 2" var ((c - a * b) / (coeff * b))
      return Eliminated
    (Uninomial av as' _ _, Uninomial bv bs' _ _) -> return $ shrinkedOrStuck [av, bv] $ MulConstraint as' bs' (Left c)
    (Uninomial av as' _ _, Polynomial bv bs') -> return $ shrinkedOrStuck [av, bv] $ MulConstraint as' bs' (Left c)
    (Polynomial _ as', Constant b) -> case Poly.multiplyBy b as' of
      Left constant -> eliminateIfHold constant c
      Right poly -> return $ Shrinked $ AddConstraint $ Poly.addConstant (-c) poly
    (Polynomial av as', Uninomial bv bs' _ _) -> return $ shrinkedOrStuck [av, bv] $ MulConstraint as' bs' (Left c)
    (Polynomial av as', Polynomial bv bs') -> return $ shrinkedOrStuck [av, bv] $ MulConstraint as' bs' (Left c)
shrinkMul as bs (Right cs) = do
  bindings <- get
  case (substAndView bindings as, substAndView bindings bs, substAndView bindings cs) of
    (Constant a, Constant b, Constant c) -> eliminateIfHold (a * b) c
    (Constant a, Constant b, Uninomial _ _ c (var, coeff)) -> do
      -- a * b - c = coeff var
      bindVar "mul 3" var ((a * b - c) / coeff)
      return Eliminated
    (Constant a, Constant b, Polynomial _ cs') -> return $ Shrinked $ AddConstraint (Poly.addConstant (-a * b) cs')
    -- return $ Shrinked $ R1C (Left a) (Left b) (Right cs')
    (Constant a, Uninomial _ _ b (var, coeff), Constant c) -> do
      if a == 0
        then eliminateIfHold (a * b) c
        else do
          -- a * (b + coeff var) = c
          --    =>
          -- a * b + a * coeff * var = c
          --    =>
          -- a * coeff * var = c - a * b
          --    =>
          -- var = (c - a * b) / (coeff * a)
          bindVar "mul 4" var ((c - a * b) / (coeff * a))
          return Eliminated
    (Constant a, Uninomial _ bs' _ _, Uninomial _ cs' _ _) -> case Poly.multiplyBy (-a) bs' of
      Left constant -> return $ Shrinked $ AddConstraint (Poly.addConstant constant cs')
      Right poly -> case Poly.merge poly cs' of
        Left constant -> eliminateIfHold constant 0
        Right poly' -> return $ Shrinked $ AddConstraint poly'
    (Constant a, Uninomial _ bs' _ _, Polynomial _ cs') -> case Poly.multiplyBy (-a) bs' of
      Left constant -> return $ Shrinked $ AddConstraint (Poly.addConstant constant cs')
      Right poly -> case Poly.merge poly cs' of
        Left constant -> eliminateIfHold constant 0
        Right poly' -> return $ Shrinked $ AddConstraint poly'
    (Constant a, Polynomial _ bs', Constant c) -> case Poly.multiplyBy (-a) bs' of
      Left constant -> eliminateIfHold constant c
      Right poly -> return $ Shrinked $ AddConstraint (Poly.addConstant c poly)
    (Constant a, Polynomial _ bs', Uninomial _ cs' _ _) -> case Poly.multiplyBy (-a) bs' of
      Left constant -> return $ Shrinked $ AddConstraint (Poly.addConstant constant cs')
      Right poly -> case Poly.merge poly cs' of
        Left constant -> eliminateIfHold constant 0
        Right poly' -> return $ Shrinked $ AddConstraint poly'
    (Constant a, Polynomial _ bs', Polynomial _ cs') -> case Poly.multiplyBy (-a) bs' of
      Left constant -> return $ Shrinked $ AddConstraint (Poly.addConstant constant cs')
      Right poly -> case Poly.merge poly cs' of
        Left constant -> eliminateIfHold constant 0
        Right poly' -> return $ Shrinked $ AddConstraint poly'
    (Uninomial _ _ a (var, coeff), Constant b, Constant c) -> do
      if b == 0
        then eliminateIfHold 0 c
        else do
          -- (a + coeff var) * b = c
          bindVar "mul 5" var ((c - a * b) / (coeff * b))
          return Eliminated
    (Uninomial _ as' _ _, Constant b, Uninomial _ cs' _ _) -> case Poly.multiplyBy (-b) as' of
      Left constant -> return $ Shrinked $ AddConstraint (Poly.addConstant constant cs')
      Right poly -> case Poly.merge poly cs' of
        Left constant -> eliminateIfHold constant 0
        Right poly' -> return $ Shrinked $ AddConstraint poly'
    (Uninomial _ as' _ _, Constant b, Polynomial _ cs') -> case Poly.multiplyBy (-b) as' of
      Left constant -> return $ Shrinked $ AddConstraint (Poly.addConstant constant cs')
      Right poly -> case Poly.merge poly cs' of
        Left constant -> eliminateIfHold constant 0
        Right poly' -> return $ Shrinked $ AddConstraint poly'
    (Uninomial _ as' _ _, Uninomial _ bs' _ _, Constant c) -> return $ Shrinked $ MulConstraint as' bs' (Left c)
    (Uninomial av as' _ _, Uninomial bv bs' _ _, Uninomial cv cs' _ _) -> return $ shrinkedOrStuck [av, bv, cv] $ MulConstraint as' bs' (Right cs')
    (Uninomial av as' _ _, Uninomial bv bs' _ _, Polynomial cv cs') -> return $ shrinkedOrStuck [av, bv, cv] $ MulConstraint as' bs' (Right cs')
    (Uninomial _ as' _ _, Polynomial _ bs', Constant c) -> return $ Shrinked $ MulConstraint as' bs' (Left c)
    (Uninomial av as' _ _, Polynomial bv bs', Uninomial cv cs' _ _) -> return $ shrinkedOrStuck [av, bv, cv] $ MulConstraint as' bs' (Right cs')
    (Uninomial av as' _ _, Polynomial bv bs', Polynomial cv cs') -> return $ shrinkedOrStuck [av, bv, cv] $ MulConstraint as' bs' (Right cs')
    (Polynomial _ as', Constant b, Constant c) -> case Poly.multiplyBy (-b) as' of
      Left constant -> eliminateIfHold constant c
      Right poly -> return $ Shrinked $ AddConstraint (Poly.addConstant c poly)
    (Polynomial _ as', Constant b, Uninomial _ cs' _ _) -> case Poly.multiplyBy (-b) as' of
      Left constant -> return $ Shrinked $ AddConstraint (Poly.addConstant constant cs')
      Right poly -> case Poly.merge poly cs' of
        Left constant -> eliminateIfHold constant 0
        Right poly' -> return $ Shrinked $ AddConstraint poly'
    (Polynomial _ as', Constant b, Polynomial _ cs') -> case Poly.multiplyBy (-b) as' of
      Left constant -> return $ Shrinked $ AddConstraint (Poly.addConstant constant cs')
      Right poly -> case Poly.merge poly cs' of
        Left constant -> eliminateIfHold constant 0
        Right poly' -> return $ Shrinked $ AddConstraint poly'
    (Polynomial _ as', Uninomial _ bs' _ _, Constant c) -> return $ Shrinked $ MulConstraint as' bs' (Left c)
    (Polynomial av as', Uninomial bv bs' _ _, Uninomial cv cs' _ _) -> return $ shrinkedOrStuck [av, bv, cv] $ MulConstraint as' bs' (Right cs')
    (Polynomial av as', Uninomial bv bs' _ _, Polynomial cv cs') -> return $ shrinkedOrStuck [av, bv, cv] $ MulConstraint as' bs' (Right cs')
    (Polynomial _ as', Polynomial _ bs', Constant c) -> return $ Shrinked $ MulConstraint as' bs' (Left c)
    (Polynomial av as', Polynomial bv bs', Uninomial cv cs' _ _) -> return $ shrinkedOrStuck [av, bv, cv] $ MulConstraint as' bs' (Right cs')
    (Polynomial av as', Polynomial bv bs', Polynomial cv cs') -> return $ shrinkedOrStuck [av, bv, cv] $ MulConstraint as' bs' (Right cs')

eliminateIfHold :: (GaloisField n, Integral n) => n -> n -> M n (Result a)
eliminateIfHold expected actual =
  if expected == actual
    then return Eliminated
    else throwError (ConflictingValues "at eliminateIfHold")

-- | Trying to reduce a DivMod constraint if any of these set of variables are known:
--    1. dividend & divisor
--    1. dividend & quotient
--    2. divisor & quotient & remainder
shrinkDivMod ::
  (GaloisField n, Integral n) =>
  Bool ->
  (Limbs, Limbs, Limbs, Limbs) ->
  M n (Result (Limbs, Limbs, Limbs, Limbs))
shrinkDivMod isCarryLess (dividendVar, divisorVar, quotientVar, remainderVar) = do
  -- check the value of the dividend first,
  -- if it's unknown, then its value can only be determined from other variables
  dividendResult <- lookupLimbs dividendVar
  divisorResult <- lookupLimbs divisorVar
  quotientResult <- lookupLimbs quotientVar
  remainderResult <- lookupLimbs remainderVar

  case dividendResult of
    Just dividendVal -> do
      -- now that we know the dividend, we can solve the relation if we know either the divisor or the quotient
      case (divisorResult, quotientResult, remainderResult) of
        (Just divisorVal, Just actualQuotientVal, Just actualRemainderVal) -> do
          when (toInteger divisorVal == 0) $
            throwError $
              DivisorIsZeroError divisorVar
          let (expectedQuotientVal, expectedRemainderVal) = if isCarryLess then dividendVal `U.clDivMod` divisorVal else dividendVal `divMod` divisorVal
          when (expectedQuotientVal /= actualQuotientVal) $
            throwError $
              ConflictingValues "quotient value mismatch"
          when (expectedRemainderVal /= actualRemainderVal) $
            throwError $
              ConflictingValues "remainder value mismatch"
          return Eliminated
        (Just divisorVal, Just actualQuotientVal, Nothing) -> do
          when (toInteger divisorVal == 0) $
            throwError $
              DivisorIsZeroError divisorVar
          let (expectedQuotientVal, expectedRemainderVal) = if isCarryLess then dividendVal `U.clDivMod` divisorVal else dividendVal `divMod` divisorVal
          when (expectedQuotientVal /= actualQuotientVal) $
            throwError $
              ConflictingValues "quotient value mismatch with remainder unknown"
          bindLimbs "remainder" remainderVar expectedRemainderVal
          return Eliminated
        (Just divisorVal, Nothing, Just actualRemainderVal) -> do
          when (toInteger divisorVal == 0) $
            throwError $
              DivisorIsZeroError divisorVar
          let (expectedQuotientVal, expectedRemainderVal) = if isCarryLess then dividendVal `U.clDivMod` divisorVal else dividendVal `divMod` divisorVal
          when (expectedRemainderVal /= actualRemainderVal) $
            throwError $
              ConflictingValues "remainder value mismatch with quotient unknown"
          bindLimbs "quotient" quotientVar expectedQuotientVal
          return Eliminated
        (Just divisorVal, Nothing, Nothing) -> do
          when (toInteger divisorVal == 0) $
            throwError $
              DivisorIsZeroError divisorVar
          let (expectedQuotientVal, expectedRemainderVal) = if isCarryLess then dividendVal `U.clDivMod` divisorVal else dividendVal `divMod` divisorVal
          bindLimbs "quotient" quotientVar expectedQuotientVal
          bindLimbs "remainder" remainderVar expectedRemainderVal
          return Eliminated
        (Nothing, Just actualQuotientVal, Just actualRemainderVal) -> do
          let expectedDivisorVal = if isCarryLess then dividendVal `U.clDiv` actualQuotientVal else dividendVal `div` actualQuotientVal
              expectedRemainderVal = if isCarryLess then dividendVal `U.clMod` expectedDivisorVal else dividendVal `mod` expectedDivisorVal
          when (expectedRemainderVal /= actualRemainderVal) $
            throwError $
              ConflictingValues "remainder value mismatch with divisor unknown"
          bindLimbs "divisor" divisorVar expectedDivisorVal
          return Eliminated
        (Nothing, Just actualQuotientVal, Nothing) -> do
          -- if the quotient is 0, then we know that:
          --  1. the remainder = the dividend
          --  2. the divisor > the dividend
          (expectedDivisorVal, expectedRemainderVal) <-
            if toInteger actualQuotientVal == 0
              then throwError $ QuotientIsZeroError quotientVar
              else
                if toInteger dividendVal == 0
                  then throwError $ DividendIsZeroError dividendVar
                  else return $ if isCarryLess then dividendVal `U.clDivMod` actualQuotientVal else dividendVal `divMod` actualQuotientVal
          bindLimbs "divisor" divisorVar expectedDivisorVal
          bindLimbs "remainder" remainderVar expectedRemainderVal
          return Eliminated
        _ -> return $ Stuck (dividendVar, divisorVar, quotientVar, remainderVar)
    Nothing -> do
      -- we can only piece out the dividend if all of the divisor, quotient, and remainder are known
      case (divisorResult, quotientResult, remainderResult) of
        -- divisor, quotient, and remainder are all known
        (Just divisorVal, Just quotientVal, Just remainderVal) -> do
          let dividendVal =
                if isCarryLess
                  then (divisorVal `U.clMul` quotientVal) `Data.Bits.xor` remainderVal
                  else divisorVal * quotientVal + remainderVal
          bindLimbs "dividend" dividendVar dividendVal
          return Eliminated
        _ -> do
          return $ Stuck (dividendVar, divisorVar, quotientVar, remainderVar)

-- | Trying to reduce a Boolean constraint
shrinkBooleanConstraint :: (GaloisField n, Integral n) => Var -> M n (Result Var)
shrinkBooleanConstraint var = do
  varResult <- lookupVar var
  case varResult of
    Just val ->
      if val /= 0 && val /= 1
        then throwError $ BooleanConstraintError var val
        else return Eliminated
    Nothing -> return $ Stuck var

-- | Trying to reduce a ModInv constraint
shrinkModInv ::
  (GaloisField n, Integral n) =>
  (Limbs, Limbs, Limbs, Integer) ->
  M n (Result (Limbs, Limbs, Limbs, Integer))
shrinkModInv (aLimbs, outLimbs, nLimbs, p) = do
  aResult <- lookupLimbs aLimbs
  case aResult of
    Just aVal -> do
      case U.modInv (toInteger aVal) p of
        Just result -> do
          let width = sum (map fst aLimbs)
          -- aVal * result = n * p + 1
          let nVal = U.new width ((toInteger aVal * result - 1) `div` p)
          bindLimbs "ModInv n" nLimbs nVal
          bindLimbs "ModInv" outLimbs (U.new width result)
          return Eliminated
        Nothing -> throwError $ ModInvError aLimbs p
    Nothing -> return $ Stuck (aLimbs, outLimbs, nLimbs, p)

-- if (x - y) = 0 then m = 0 else m = recip (x - y)
shrinkEqZero :: (GaloisField n, Integral n) => (Poly n, Var) -> M n (Result (Poly n, Var))
shrinkEqZero eqZero@(xs, m) = do
  bindings <- get
  case substAndView bindings xs of
    Constant 0 -> do
      bindVar "=0 0" m 0
      return Eliminated
    Constant c -> do
      bindVar "=0 recip c" m (recip c)
      return Eliminated
    Uninomial changed xs' _ _ ->
      -- only consider the polynomial shrinked if it's size has been reduced
      if changed
        then return $ Shrinked (xs', m)
        else return $ Stuck eqZero
    Polynomial changed xs' ->
      if changed
        then return $ Shrinked (xs', m)
        else return $ Stuck eqZero

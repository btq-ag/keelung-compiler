{-# LANGUAGE DeriveFunctor #-}

-- | Witness solver/generator for R1CS
module Keelung.Solver (run, debug, Error (..), detectBinRep, Log (..), LogReport (..)) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor (first)
import Data.Bits qualified
import Data.Field.Galois (GaloisField (order))
import Data.Foldable (toList)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List qualified as List
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Keelung
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Constraint.R1C
import Keelung.Constraint.R1CS
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Interpreter.Arithmetics (U (UVal))
import Keelung.Interpreter.Arithmetics qualified as U
import Keelung.Solver.Monad
import Keelung.Syntax.Counters

-- | Execute the R1CS solver
run :: (GaloisField n, Integral n) => R1CS n -> Inputs n -> Either (Error n) (Vector n, Vector n)
run r1cs inputs = fst (run' False r1cs inputs)

-- | Like `run`, but with debug logs
debug :: (GaloisField n, Integral n) => R1CS n -> Inputs n -> (Either (Error n) (Vector n, Vector n), Maybe (LogReport n))
debug = run' True

-- | Returns (interpreted outputs, witnesses, log)s
run' :: (GaloisField n, Integral n) => Bool -> R1CS n -> Inputs n -> (Either (Error n) (Vector n, Vector n), Maybe (LogReport n))
run' debugMode r1cs inputs = do
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
fromOrdinaryConstraints (R1CS _ ordinaryConstraints _ counters eqZeros divMods modInvs) = do
  constraints <- concat <$> mapM differentiate ordinaryConstraints
  return $
    Seq.fromList constraints
      <> Seq.fromList (map BooleanConstraint booleanInputVarConstraints)
      <> Seq.fromList (map EqZeroConstraint eqZeros)
      <> Seq.fromList (map DivModConstaint divMods)
      <> Seq.fromList (map ModInvConstraint modInvs)
  where
    booleanInputVarConstraints =
      let generateRange (start, end) = [start .. end - 1]
       in concatMap generateRange (getBooleanConstraintRanges counters)

    differentiate :: (GaloisField n, Integral n) => R1C n -> Either (Error n) [Constraint n]
    differentiate (R1C (Left a) (Left b) (Left c)) = if a * b == c then Right [] else Left ConflictingValues
    differentiate (R1C (Left a) (Left b) (Right c)) = Right [AddConstraint $ Poly.addConstant (-a * b) c]
    differentiate (R1C (Left a) (Right b) (Left c)) = case Poly.multiplyBy a b of
      Left constant ->
        if constant == c
          then Right []
          else Left ConflictingValues
      Right poly -> Right [AddConstraint $ Poly.addConstant (-c) poly]
    differentiate (R1C (Left a) (Right b) (Right c)) = case Poly.multiplyBy (-a) b of
      Left constant -> Right [AddConstraint $ Poly.addConstant constant c]
      Right poly -> case Poly.merge poly c of
        Left constant ->
          if constant == 0
            then Right []
            else Left ConflictingValues
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

lookupBitsEither :: (GaloisField n, Integral n) => (Width, Either Var Integer) -> M n (Maybe U)
lookupBitsEither (width, Left var) = do
  vals <- mapM lookupVar [var .. var + width - 1]
  case sequence vals of
    Nothing -> return Nothing
    Just bitVals -> return $ Just $ UVal width $ toInteger $ sum [bitVal * (2 ^ i) | (i, bitVal) <- zip [0 :: Int ..] bitVals]
lookupBitsEither (width, Right val) = return (Just (UVal width val))

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
shrink (DivModConstaint divModTuple) = fmap (pure . DivModConstaint) <$> shrinkDivMod divModTuple
-- shrink (DivModConstaint2 divModTuple) = fmap (pure . DivModConstaint) <$> shrinkDivMod divModTuple
shrink (ModInvConstraint modInvHint) = fmap (pure . ModInvConstraint) <$> shrinkModInv modInvHint

shrinkAdd :: (GaloisField n, Integral n) => Poly n -> M n (Result (Constraint n))
shrinkAdd xs = do
  bindings <- get
  -- case IntMap.member 48 (Poly.coeffs xs) of
  --   True -> do 
  --     traceShowM (fmap N xs)
  --     traceShowM (fmap N bindings)
  --   False -> return ()
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
    (Constant a, Uninomial _ _ b (var, coeff)) -> do
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
          bindVar "mul 1" var ((c - a * b) / (coeff * a))
          return Eliminated
    (Constant a, Polynomial _ bs') -> case Poly.multiplyBy a bs' of
      Left constant -> eliminateIfHold constant c
      Right poly -> return $ Shrinked $ AddConstraint $ Poly.addConstant (-c) poly
    (Uninomial _ _ a (var, coeff), Constant b) -> do
      if b == 0
        then eliminateIfHold (a * b) c
        else do
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
    else throwError ConflictingValues

-- | Trying to reduce a DivMod constraint if any of these set of variables are known:
--    1. dividend & divisor
--    1. dividend & quotient
--    2. divisor & quotient & remainder
shrinkDivMod ::
  (GaloisField n, Integral n) =>
  ((Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer)) ->
  M n (Result ((Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer)))
shrinkDivMod (dividendVar, divisorVar, quotientVar, remainderVar) = do
  -- check the value of the dividend first,
  -- if it's unknown, then its value can only be determined from other variables
  dividendResult <- lookupBitsEither dividendVar
  divisorResult <- lookupBitsEither divisorVar
  quotientResult <- lookupBitsEither quotientVar
  remainderResult <- lookupBitsEither remainderVar

  case dividendResult of
    Just dividendVal -> do
      -- now that we know the dividend, we can solve the relation if we know either the divisor or the quotient
      case (divisorResult, quotientResult, remainderResult) of
        (Just divisorVal, Just actualQuotientVal, Just actualRemainderVal) -> do
          let expectedQuotientVal = dividendVal `U.integerDivU` divisorVal
              expectedRemainderVal = dividendVal `U.integerModU` divisorVal
          when (expectedQuotientVal /= actualQuotientVal) $
            throwError ConflictingValues
          -- DivModQuotientError dividendVal divisorVal expectedQuotientVal actualQuotientVal
          when (expectedRemainderVal /= actualRemainderVal) $
            throwError ConflictingValues
          -- throwError $
          --   DivModRemainderError dividendVal divisorVal expectedRemainderVal actualRemainderVal
          return Eliminated
        (Just divisorVal, Just actualQuotientVal, Nothing) -> do
          let expectedQuotientVal = dividendVal `U.integerDivU` divisorVal
              expectedRemainderVal = dividendVal `U.integerModU` divisorVal
          when (expectedQuotientVal /= actualQuotientVal) $
            throwError ConflictingValues
          bindBitsEither "remainder" remainderVar expectedRemainderVal
          return Eliminated
        (Just divisorVal, Nothing, Just actualRemainderVal) -> do
          let expectedQuotientVal = dividendVal `U.integerDivU` divisorVal
              expectedRemainderVal = dividendVal `U.integerModU` divisorVal
          when (expectedRemainderVal /= actualRemainderVal) $
            throwError ConflictingValues
          bindBitsEither "quotient" quotientVar expectedQuotientVal
          return Eliminated
        (Just divisorVal, Nothing, Nothing) -> do
          let expectedQuotientVal = dividendVal `U.integerDivU` divisorVal
              expectedRemainderVal = dividendVal `U.integerModU` divisorVal
          bindBitsEither "quotient" quotientVar expectedQuotientVal
          bindBitsEither "remainder" remainderVar expectedRemainderVal
          return Eliminated
        (Nothing, Just actualQuotientVal, Just actualRemainderVal) -> do
          let expectedDivisorVal = dividendVal `U.integerDivU` actualQuotientVal
              expectedRemainderVal = dividendVal `U.integerModU` expectedDivisorVal
          when (expectedRemainderVal /= actualRemainderVal) $
            throwError ConflictingValues
          bindBitsEither "divisor" divisorVar expectedDivisorVal
          return Eliminated
        (Nothing, Just actualQuotientVal, Nothing) -> do
          let expectedDivisorVal = dividendVal `U.integerDivU` actualQuotientVal
              expectedRemainderVal = dividendVal `U.integerModU` expectedDivisorVal
          bindBitsEither "divisor" divisorVar expectedDivisorVal
          bindBitsEither "remainder" remainderVar expectedRemainderVal
          return Eliminated
        _ -> return $ Stuck (dividendVar, divisorVar, quotientVar, remainderVar)
    Nothing -> do
      -- we can only piece out the dividend if all of the divisor, quotient, and remainder are known
      case (divisorResult, quotientResult, remainderResult) of
        -- divisor, quotient, and remainder are all known
        (Just divisorVal, Just quotientVal, Just remainderVal) -> do
          let dividendVal = (divisorVal `U.integerMulU` quotientVal) `U.integerAddU` remainderVal
          bindBitsEither "divident" dividendVar dividendVal
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
  ((Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer), Integer) ->
  M n (Result ((Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer), Integer))
shrinkModInv (aVar, outVar, nVar, p) = do
  aResult <- lookupBitsEither aVar
  case aResult of
    Just aVal -> do
      case U.modInv (U.uintValue aVal) p of
        Just result -> do
          let (width, _) = aVar
          -- aVal * result = n * p + 1
          let nVal = (aVal `U.integerMulU` UVal width result `U.integerSubU` UVal width 1) `U.integerDivU` UVal width p
          bindBitsEither "ModInv n" nVar nVal
          bindBitsEither "ModInv" outVar (UVal width result)
          return Eliminated
        Nothing -> throwError $ ModInvError aVar p
    Nothing -> return $ Stuck (aVar, outVar, nVar, p)

-- | Trying to reduce a BinRep constraint
data FoldState n = Start | Failed | Continue n (IntMap (Bool, Var)) deriving (Eq, Show)

-- | Given a mapping of (Int, (Bool, Var)) pairs, where the Int indicates the power of 2, and the Bool indicates whether the coefficient is positive or negative
--   and an Integer, derive coefficients (Boolean) for each of these variables such that the sum of the coefficients times the powers of 2 is equal to the Integer
deriveCoeffs :: (GaloisField n, Integral n) => n -> IntMap (Bool, Var) -> [(Var, Bool)]
deriveCoeffs rawConstant polynomial =
  let negatedPolynomial = fmap (first not) polynomial
      (upper, lower) = boundsOf negatedPolynomial
      constant = toInteger rawConstant
      negatedConstant = negate (toInteger (order rawConstant - fromIntegral rawConstant))
      -- should flip the sign if the constant is outside the bounds of the polynomial
      shouldFlipSign = upper < negatedConstant || lower > negatedConstant
   in fst $ IntMap.foldlWithKey' go ([], if shouldFlipSign then constant else negatedConstant) polynomial
  where
    -- given coefficients, calculate the upper bound and the lower bound of the polynomial
    boundsOf :: IntMap (Bool, Var) -> (Integer, Integer)
    boundsOf =
      IntMap.foldlWithKey'
        ( \(upper, lower) power (sign, _) ->
            if sign then (upper + (2 ^ power), lower) else (upper, lower - (2 ^ power))
        )
        (0, 0)

    go :: ([(Var, Bool)], Integer) -> Int -> (Bool, Var) -> ([(Var, Bool)], Integer)
    go (acc, c) power (sign, var) =
      if Data.Bits.testBit c power
        then
          if sign
            then ((var, True) : acc, c + (2 ^ power))
            else ((var, True) : acc, c - (2 ^ power))
        else ((var, False) : acc, c)

-- | Reduce binary representations
shrinkBinRep :: (GaloisField n, Integral n) => Result (Constraint n) -> M n (Result (Constraint n))
shrinkBinRep NothingToDo = return NothingToDo
shrinkBinRep Eliminated = return Eliminated
shrinkBinRep (Shrinked polynomial) = return (Shrinked polynomial)
shrinkBinRep (Stuck (AddConstraint polynomial)) = do
  Env _ boolVarRanges fieldBitWidth <- ask
  let isBoolean var = case IntMap.lookupLE var boolVarRanges of
        Nothing -> False
        Just (index, len) -> var < index + len
  case detectBinRep fieldBitWidth isBoolean polynomial of
    Nothing -> return (Stuck (AddConstraint polynomial))
    Just assignments -> do
      -- we have a binary representation
      -- we can now assign the variables
      forM_ assignments $ \(var, val) -> do
        bindVar "bin rep" var (if val then 1 else 0)
      return Eliminated
shrinkBinRep (Stuck polynomial) = return (Stuck polynomial)

-- | Watch out for a stuck R1C, and see if it's a binary representation
--    1. see if variables are all Boolean
--    2. see if coefficients are all multiples of powers of 2
--    3. see if these powers of 2 are all unique
--
--   Property:
--    For a field of order `n`, let `k = floor(log2(n))`, i.e., the number of bits that can be fit into a field element.
--    1. There can be at most `k` coefficients that are multiples of powers of 2 if the polynomial is a binary representation.
--    2. These coefficients cannot be too far apart, i.e., the quotient of any 2 coefficients cannot be greater than `2^(k-1)`.
--    3. For any 2 coefficients `a` and `b`, either `a / b` or `b / a` must be a power of 2 smaller than `2^k`.
detectBinRep :: (GaloisField n, Integral n) => Width -> (Var -> Bool) -> Poly n -> Maybe [(Var, Bool)]
detectBinRep fieldBitWidth isBoolean polynomial =
  if IntMap.size (Poly.coeffs polynomial) > fromIntegral fieldBitWidth
    then Nothing
    else case collectCoeffs polynomial of
      Start -> Nothing
      Failed -> Nothing
      Continue picked invertedPolynomial ->
        let powers = IntMap.keys invertedPolynomial
            powersAllUnique = length powers == length (List.nub powers)
         in if powersAllUnique
              then case IntMap.lookupMin invertedPolynomial of
                Nothing -> Just []
                Just (minPower, _) ->
                  -- if the smallest power is negative, make it 2^0
                  if minPower < 0
                    then
                      let normalizedPolynomial = IntMap.mapKeys (\i -> i - minPower) invertedPolynomial
                          constant = Poly.constant polynomial * (2 ^ (-minPower)) / picked
                       in Just (deriveCoeffs constant normalizedPolynomial)
                    else Just (deriveCoeffs (Poly.constant polynomial / picked) invertedPolynomial)
              else Nothing
  where
    collectCoeffs :: (GaloisField n, Integral n) => Poly n -> FoldState n
    collectCoeffs xs = IntMap.foldlWithKey' go Start (Poly.coeffs xs)
      where
        go :: (GaloisField n, Integral n) => FoldState n -> Var -> n -> FoldState n
        go Start var coeff =
          if isBoolean var
            then -- since this is the first coefficient, we can always assume that it's a power of 2
              Continue coeff (IntMap.singleton 0 (True, var))
            else Failed
        go Failed _ _ = Failed
        go (Continue picked coeffs) var coeff =
          if isBoolean var
            then
              let result = case isPowerOf2' fieldBitWidth (coeff / picked) of
                    Just power -> Just (power, True)
                    Nothing -> case isPowerOf2' fieldBitWidth (picked / coeff) of
                      Just power -> Just (-power, True)
                      Nothing -> case isPowerOf2' fieldBitWidth ((-coeff) / picked) of
                        Just power -> Just (power, False)
                        Nothing -> case isPowerOf2' fieldBitWidth (picked / (-coeff)) of
                          Just power -> Just (-power, False)
                          Nothing -> Nothing
               in case result of
                    Nothing -> Failed
                    Just (power, sign) ->
                      case IntMap.lookup power coeffs of
                        Nothing -> Continue picked (IntMap.insert power (sign, var) coeffs)
                        Just _ -> Failed
            else Failed

-- | See if a coefficient is a power of 2
--   Note that, because these coefficients are field elements,
--    they can be powers of 2 when viewed as either "positive integers" or "negative integers"
isPowerOf2' :: (GaloisField n, Integral n) => Width -> n -> Maybe Int
isPowerOf2' _ 1 = Nothing
isPowerOf2' _ 2 = Just 1
isPowerOf2' fieldBitWidth coeff =
  case check (toInteger coeff) of
    Nothing -> Nothing
    Just 0 -> Nothing --
    Just result ->
      if result >= fieldBitWidth
        then Nothing
        else Just result
  where
    -- Speed this up
    check :: Integer -> Maybe Int
    check n =
      let expected = floor (logBase 2 (fromInteger (abs n)) :: Double)
       in if abs n == 2 ^ expected
            then Just expected
            else Nothing

-- isPowerOf2 :: (GaloisField n, Integral n) => n -> Maybe (Bool, Int)
-- isPowerOf2 (-2) = Just (False, 1)
-- isPowerOf2 (-1) = Just (False, 0)
-- isPowerOf2 1 = Just (True, 0)
-- isPowerOf2 2 = Just (True, 1)
-- isPowerOf2 coeff =
--   let asInteger = toInteger coeff
--    in if even asInteger
--         then (True,) <$> check asInteger
--         else (False,) <$> check (negate (fromIntegral (order coeff) - fromIntegral coeff))
--   where
--     -- Speed this up
--     check :: Integer -> Maybe Int
--     check n =
--       let expected = floor (logBase 2 (fromInteger (abs n)) :: Double)
--        in if abs n == 2 ^ expected
--             then Just expected
--             else Nothing

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

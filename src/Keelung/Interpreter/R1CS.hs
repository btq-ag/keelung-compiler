{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Interpreter.R1CS (run, run', Error (..)) where

import Control.Monad.Except
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Keelung.Compiler.Syntax.FieldBits (toBits)
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Constraint.R1C
import Keelung.Constraint.R1CS
import Keelung.Data.BinRep (BinRep (..))
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Interpreter.Arithmetics qualified as Arithmetics
import Keelung.Interpreter.R1CS.Monad
import Keelung.Syntax (Var)
import Keelung.Syntax.Counters

run :: (GaloisField n, Integral n) => R1CS n -> Inputs n -> Either (Error n) [n]
run r1cs inputs = fst <$> run' r1cs inputs

-- | Return interpreted outputs along with the witnesses
run' :: (GaloisField n, Integral n) => R1CS n -> Inputs n -> Either (Error n) ([n], Vector n)
run' r1cs inputs = do
  let constraints = fromOrdinaryConstraints r1cs
  witness <- runM inputs $ goThroughManyTimes constraints

  -- extract output values from the witness
  let outputVars = enumerate $ getRanges (r1csCounters r1cs) [OutputField .. OutputUInt]
        -- [start .. end - 1]
  let outputs = map (witness Vector.!) outputVars

  return (outputs, witness)

-- | Return Constraints from a R1CS, which include:
--   1. ordinary constraints
--   2. Boolean input variable constraints
--   3. binary representation constraints
--   4. CNEQ constraints
fromOrdinaryConstraints :: (GaloisField n, Integral n) => R1CS n -> Seq (Constraint n)
fromOrdinaryConstraints (R1CS _ ordinaryConstraints binReps counters eqZeros divMods modInvs) =
  Seq.fromList (map R1CConstraint ordinaryConstraints)
    <> Seq.fromList (map BooleanConstraint booleanInputVarConstraints)
    <> Seq.fromList (map BinRepConstraint binReps)
    -- <> Seq.fromList (map (BinRepConstraint2 . toList) binReps')
    <> Seq.fromList (map EqZeroConstraint eqZeros)
    <> Seq.fromList (map DivModConstaint divMods)
    <> Seq.fromList (map ModInvConstraint modInvs)
  where
    booleanInputVarConstraints =
      let generate (start, end) = [start .. end - 1]
       in concatMap generate (getBooleanConstraintRanges counters)

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

lookupVarEither :: Either Var n -> M n (Maybe n)
lookupVarEither (Left var) = lookupVar var
lookupVarEither (Right val) = return (Just val)

shrink :: (GaloisField n, Integral n) => Constraint n -> M n (Result (Seq (Constraint n)))
shrink (R1CConstraint r1c) = fmap (pure . R1CConstraint) <$> shrinkR1C r1c
shrink (BooleanConstraint var) = fmap (pure . BooleanConstraint) <$> shrinkBooleanConstraint var
shrink (EqZeroConstraint eqZero) = fmap (pure . EqZeroConstraint) <$> shrinkEqZero eqZero
shrink (DivModConstaint divModTuple) = fmap (pure . DivModConstaint) <$> shrinkDivMod divModTuple
shrink (BinRepConstraint binRep) = fmap (pure . BinRepConstraint) <$> shrinkBinRep binRep
shrink (BinRepConstraint2 binRep) = fmap (pure . BinRepConstraint2) <$> shrinkBinRep2 binRep
shrink (ModInvConstraint modInv) = fmap (pure . ModInvConstraint) <$> shrinkModInv modInv

-- | Trying to reduce a DivMod constraint if any of these set of variables are known:
--    1. dividend & divisor
--    1. dividend & quotient
--    2. divisor & quotient & remainder
shrinkDivMod :: (GaloisField n, Integral n) => (Either Var n, Either Var n, Either Var n, Either Var n) -> M n (Result (Either Var n, Either Var n, Either Var n, Either Var n))
shrinkDivMod (dividendVar, divisorVar, quotientVar, remainderVar) = do
  -- check the value of the dividend first,
  -- if it's unknown, then its value can only be determined from other variables
  dividendResult <- lookupVarEither dividendVar
  divisorResult <- lookupVarEither divisorVar
  quotientResult <- lookupVarEither quotientVar
  remainderResult <- lookupVarEither remainderVar
  case dividendResult of
    Just dividendVal -> do
      -- now that we know the dividend, we can solve the relation if we know either the divisor or the quotient
      case (divisorResult, quotientResult, remainderResult) of
        (Just divisorVal, Just actualQuotientVal, Just actualRemainderVal) -> do
          let expectedQuotientVal = dividendVal `Arithmetics.integerDiv` divisorVal
              expectedRemainderVal = dividendVal `Arithmetics.integerMod` divisorVal
          when (expectedQuotientVal /= actualQuotientVal) $
            throwError $
              DivModQuotientError dividendVal divisorVal expectedQuotientVal actualQuotientVal
          when (expectedRemainderVal /= actualRemainderVal) $
            throwError $
              DivModRemainderError dividendVal divisorVal expectedRemainderVal actualRemainderVal
          return Eliminated
        (Just divisorVal, Just actualQuotientVal, Nothing) -> do
          let expectedQuotientVal = dividendVal `Arithmetics.integerDiv` divisorVal
              expectedRemainderVal = dividendVal `Arithmetics.integerMod` divisorVal
          when (expectedQuotientVal /= actualQuotientVal) $
            throwError $
              DivModQuotientError dividendVal divisorVal expectedQuotientVal actualQuotientVal
          bindVarEither remainderVar expectedRemainderVal
          return Eliminated
        (Just divisorVal, Nothing, Just actualRemainderVal) -> do
          let expectedQuotientVal = dividendVal `Arithmetics.integerDiv` divisorVal
              expectedRemainderVal = dividendVal `Arithmetics.integerMod` divisorVal
          when (expectedRemainderVal /= actualRemainderVal) $
            throwError $
              DivModRemainderError dividendVal divisorVal expectedRemainderVal actualRemainderVal
          bindVarEither quotientVar expectedQuotientVal
          return Eliminated
        (Just divisorVal, Nothing, Nothing) -> do
          let expectedQuotientVal = dividendVal `Arithmetics.integerDiv` divisorVal
              expectedRemainderVal = dividendVal `Arithmetics.integerMod` divisorVal
          bindVarEither quotientVar expectedQuotientVal
          bindVarEither remainderVar expectedRemainderVal
          return Eliminated
        (Nothing, Just actualQuotientVal, Just actualRemainderVal) -> do
          let expectedDivisorVal = dividendVal `Arithmetics.integerDiv` actualQuotientVal
              expectedRemainderVal = dividendVal `Arithmetics.integerMod` expectedDivisorVal
          when (expectedRemainderVal /= actualRemainderVal) $
            throwError $
              DivModRemainderError dividendVal expectedDivisorVal expectedRemainderVal actualRemainderVal
          bindVarEither divisorVar expectedDivisorVal
          return Eliminated
        (Nothing, Just actualQuotientVal, Nothing) -> do
          let expectedDivisorVal = dividendVal `Arithmetics.integerDiv` actualQuotientVal
              expectedRemainderVal = dividendVal `Arithmetics.integerMod` expectedDivisorVal
          bindVarEither divisorVar expectedDivisorVal
          bindVarEither remainderVar expectedRemainderVal
          return Eliminated
        _ -> return $ Stuck (dividendVar, divisorVar, quotientVar, remainderVar)
    Nothing -> do
      -- we can only piece out the dividend if all of the divisor, quotient, and remainder are known
      case (divisorResult, quotientResult, remainderResult) of
        -- divisor, quotient, and remainder are all known
        (Just divisorVal, Just quotientVal, Just remainderVal) -> do
          let dividendVal = divisorVal * quotientVal + remainderVal
          bindVarEither dividendVar dividendVal
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
shrinkModInv :: (GaloisField n, Integral n) => (Either Var n, Either Var n, Integer) -> M n (Result (Either Var n, Either Var n, Integer))
shrinkModInv (aVar, nVar, p) = do
  aResult <- lookupVarEither aVar
  case aResult of
    Just aVal -> do
      case Arithmetics.modInv (toInteger aVal) p of
        Just result -> do
          -- aVal * result = n * p + 1
          let nVal = (aVal * fromInteger result - 1) `Arithmetics.integerDiv` fromInteger p
          bindVarEither nVar nVal
          return Eliminated
        Nothing -> throwError $ ModInvError aVar aVal p
    Nothing -> return $ Stuck (aVar, nVar, p)

-- | Trying to reduce a BinRep constraint
shrinkBinRep :: (GaloisField n, Integral n) => BinRep -> M n (Result BinRep)
shrinkBinRep binRep@(BinRep var width bitVarStart) = do
  varResult <- lookupVar var
  case varResult of
    -- value of "var" is known
    Just val -> do
      let bitVals = toBits val
      forM_ (zip [bitVarStart .. bitVarStart + width - 1] bitVals) $ \(bitVar, bitVal) -> do
        bindVar bitVar bitVal
      return Eliminated
    Nothing -> do
      -- see if all bit variables are bound
      bitVal <- foldM go (Just 0) [bitVarStart + width - 1, bitVarStart + width - 2 .. bitVarStart]
      case bitVal of
        Nothing -> return $ Stuck binRep
        Just bitVal' -> do
          bindVar var bitVal'
          return Eliminated
  where
    go acc bitVar = case acc of
      Nothing -> return Nothing
      Just accVal -> do
        bitValue <- lookupVar bitVar
        case bitValue of
          Nothing -> return Nothing
          Just bit -> return (Just (accVal * 2 + bit))

-- | Trying to reduce a BinRep constraint
shrinkBinRep2 :: (GaloisField n, Integral n) => [(Var, Int)] -> M n (Result [(Var, Int)])
shrinkBinRep2 _segments = do
  return Eliminated

-- if (x - y) = 0 then m = 0 else m = recip (x - y)
shrinkEqZero :: (GaloisField n, Integral n) => (Poly n, Var) -> M n (Result (Poly n, Var))
shrinkEqZero eqZero@(xs, m) = do
  bindings <- get
  case substAndView bindings xs of
    Constant 0 -> do
      bindVar m 0
      return Eliminated
    Constant c -> do
      bindVar m (recip c)
      return Eliminated
    Uninomial xs' _ _ ->
      -- only consider the polynomial shrinked if it's size has been reduced
      if Poly.varSize xs == 1
        then return $ Stuck eqZero
        else return $ Shrinked (xs', m)
    Polynomial xs' -> return $ Shrinked (xs', m)

--------------------------------------------------------------------------------

-- | Result of shrinking a constraint
data Result a = Shrinked a | Stuck a | Eliminated | NothingToDo
  deriving (Eq, Show)

instance Semigroup a => Semigroup (Result a) where
  NothingToDo <> x = x
  x <> NothingToDo = x
  Shrinked x <> Shrinked y = Shrinked (x <> y)
  Shrinked x <> Stuck y = Shrinked (x <> y)
  Shrinked x <> Eliminated = Shrinked x
  Stuck x <> Shrinked y = Shrinked (x <> y)
  Stuck x <> Stuck y = Stuck (x <> y)
  Stuck x <> Eliminated = Shrinked x
  Eliminated <> Shrinked x = Shrinked x
  Eliminated <> Stuck x = Shrinked x
  Eliminated <> Eliminated = Eliminated

instance Monoid a => Monoid (Result a) where
  mempty = NothingToDo

instance Functor Result where
  fmap f (Shrinked x) = Shrinked (f x)
  fmap f (Stuck x) = Stuck (f x)
  fmap _ Eliminated = Eliminated
  fmap _ NothingToDo = NothingToDo

shrinkR1C :: (GaloisField n, Integral n) => R1C n -> M n (Result (R1C n))
shrinkR1C r1c = do
  bindings <- get
  case r1c of
    R1C (Left a) (Left b) (Left c) -> eliminatedIfHold a b c
    R1C (Left a) (Left b) (Right cs) -> case substAndView bindings cs of
      Constant c -> eliminatedIfHold a b c
      Uninomial _ c (var, coeff) -> do
        -- a * b - c = coeff var
        bindVar var ((a * b - c) / coeff)
        return Eliminated
      Polynomial cs' -> return $ Stuck $ R1C (Left a) (Left b) (Right cs')
    R1C (Left a) (Right bs) (Left c) -> case substAndView bindings bs of
      Constant b -> eliminatedIfHold a b c
      Uninomial _ b (var, coeff) -> do
        if a == 0
          then eliminatedIfHold a b c
          else do
            -- a * (b + coeff var) = c
            --    =>
            -- a * b + a * coeff * var = c
            --    =>
            -- a * coeff * var = c - a * b
            --    =>
            -- var = (c - a * b) / (coeff * a)
            bindVar var ((c - a * b) / (coeff * a))
            return Eliminated
      Polynomial bs' -> return $ Stuck $ R1C (Left a) (Right bs') (Left c)
    R1C (Left a) (Right bs) (Right cs) -> case (substAndView bindings bs, substAndView bindings cs) of
      (Constant b, Constant c) -> eliminatedIfHold a b c
      (Constant b, Uninomial _ c (var, coeff)) -> do
        -- a * b - c = coeff var
        bindVar var ((a * b - c) / coeff)
        return Eliminated
      (Constant b, Polynomial cs') -> return $ Stuck $ R1C (Left a) (Left b) (Right cs')
      (Uninomial _ b (var, coeff), Constant c) ->
        if a == 0
          then eliminatedIfHold a b c
          else do
            -- a * (b + coeff var) = c
            bindVar var ((c - a * b) / (coeff * a))
            return Eliminated
      (Uninomial bs' _ _, Uninomial cs' _ _) -> return $ Stuck $ R1C (Left a) (Right bs') (Right cs')
      (Uninomial bs' _ _, Polynomial cs') -> return $ Stuck $ R1C (Left a) (Right bs') (Right cs')
      (Polynomial bs', Constant c) -> return $ Stuck $ R1C (Left a) (Right bs') (Left c)
      (Polynomial bs', Uninomial cs' _ _) -> return $ Stuck $ R1C (Left a) (Right bs') (Right cs')
      (Polynomial bs', Polynomial cs') -> return $ Stuck $ R1C (Left a) (Right bs') (Right cs')
    R1C (Right as) (Left b) (Left c) -> shrinkR1C $ R1C (Left b) (Right as) (Left c)
    R1C (Right as) (Left b) (Right cs) -> shrinkR1C $ R1C (Left b) (Right as) (Right cs)
    R1C (Right as) (Right bs) (Left c) -> case (substAndView bindings as, substAndView bindings bs) of
      (Constant a, Constant b) -> eliminatedIfHold a b c
      (Constant a, Uninomial _ b (var, coeff)) -> do
        if a == 0
          then eliminatedIfHold a b c
          else do
            -- a * (b + coeff var) = c
            --    =>
            -- a * b + a * coeff * var = c
            --    =>
            -- a * coeff * var = c - a * b
            --    =>
            -- var = (c - a * b) / (coeff * a)
            bindVar var ((c - a * b) / (coeff * a))
            return Eliminated
      (Constant a, Polynomial bs') -> return $ Stuck $ R1C (Left a) (Right bs') (Left c)
      (Uninomial _ a (var, coeff), Constant b) -> do
        if b == 0
          then eliminatedIfHold a b c
          else do
            -- (a + coeff var) * b = c
            bindVar var ((c - a * b) / (coeff * b))
            return Eliminated
      (Uninomial as' _ _, Uninomial bs' _ _) -> return $ Stuck $ R1C (Right as') (Right bs') (Left c)
      (Uninomial as' _ _, Polynomial bs') -> return $ Stuck $ R1C (Right as') (Right bs') (Left c)
      (Polynomial as', Constant b) -> return $ Stuck $ R1C (Right as') (Left b) (Left c)
      (Polynomial as', Uninomial bs' _ _) -> return $ Stuck $ R1C (Right as') (Right bs') (Left c)
      (Polynomial as', Polynomial bs') -> return $ Stuck $ R1C (Right as') (Right bs') (Left c)
    R1C (Right as) (Right bs) (Right cs) -> case (substAndView bindings as, substAndView bindings bs, substAndView bindings cs) of
      (Constant a, Constant b, Constant c) -> eliminatedIfHold a b c
      (Constant a, Constant b, Uninomial _ c (var, coeff)) -> do
        -- a * b - c = coeff var
        bindVar var ((a * b - c) / coeff)
        return Eliminated
      (Constant a, Constant b, Polynomial cs') -> return $ Stuck $ R1C (Left a) (Left b) (Right cs')
      (Constant a, Uninomial _ b (var, coeff), Constant c) -> do
        if a == 0
          then eliminatedIfHold a b c
          else do
            -- a * (b + coeff var) = c
            --    =>
            -- a * b + a * coeff * var = c
            --    =>
            -- a * coeff * var = c - a * b
            --    =>
            -- var = (c - a * b) / (coeff * a)
            bindVar var ((c - a * b) / (coeff * a))
            return Eliminated
      (Constant a, Uninomial bs' _ _, Uninomial cs' _ _) -> return $ Stuck $ R1C (Left a) (Right bs') (Right cs')
      (Constant a, Uninomial bs' _ _, Polynomial cs') -> return $ Stuck $ R1C (Left a) (Right bs') (Right cs')
      (Constant a, Polynomial bs', Constant c) -> return $ Stuck $ R1C (Left a) (Right bs') (Left c)
      (Constant a, Polynomial bs', Uninomial cs' _ _) -> return $ Stuck $ R1C (Left a) (Right bs') (Right cs')
      (Constant a, Polynomial bs', Polynomial cs') -> return $ Stuck $ R1C (Left a) (Right bs') (Right cs')
      (Uninomial _ a (var, coeff), Constant b, Constant c) -> do
        if b == 0
          then eliminatedIfHold a b c
          else do
            -- (a + coeff var) * b = c
            bindVar var ((c - a * b) / (coeff * b))
            return Eliminated
      (Uninomial as' _ _, Constant b, Uninomial cs' _ _) -> return $ Stuck $ R1C (Right as') (Left b) (Right cs')
      (Uninomial as' _ _, Constant b, Polynomial cs') -> return $ Stuck $ R1C (Right as') (Left b) (Right cs')
      (Uninomial as' _ _, Uninomial bs' _ _, Constant c) -> return $ Stuck $ R1C (Right as') (Right bs') (Left c)
      (Uninomial as' _ _, Uninomial bs' _ _, Uninomial cs' _ _) -> return $ Stuck $ R1C (Right as') (Right bs') (Right cs')
      (Uninomial as' _ _, Uninomial bs' _ _, Polynomial cs') -> return $ Stuck $ R1C (Right as') (Right bs') (Right cs')
      (Uninomial as' _ _, Polynomial bs', Constant c) -> return $ Stuck $ R1C (Right as') (Right bs') (Left c)
      (Uninomial as' _ _, Polynomial bs', Uninomial cs' _ _) -> return $ Stuck $ R1C (Right as') (Right bs') (Right cs')
      (Uninomial as' _ _, Polynomial bs', Polynomial cs') -> return $ Stuck $ R1C (Right as') (Right bs') (Right cs')
      (Polynomial as', Constant b, Constant c) -> return $ Stuck $ R1C (Right as') (Left b) (Left c)
      (Polynomial as', Constant b, Uninomial cs' _ _) -> return $ Stuck $ R1C (Right as') (Left b) (Right cs')
      (Polynomial as', Constant b, Polynomial cs') -> return $ Stuck $ R1C (Right as') (Left b) (Right cs')
      (Polynomial as', Uninomial bs' _ _, Constant c) -> return $ Stuck $ R1C (Right as') (Right bs') (Left c)
      (Polynomial as', Uninomial bs' _ _, Uninomial cs' _ _) -> return $ Stuck $ R1C (Right as') (Right bs') (Right cs')
      (Polynomial as', Uninomial bs' _ _, Polynomial cs') -> return $ Stuck $ R1C (Right as') (Right bs') (Right cs')
      (Polynomial as', Polynomial bs', Constant c) -> return $ Stuck $ R1C (Right as') (Right bs') (Left c)
      (Polynomial as', Polynomial bs', Uninomial cs' _ _) -> return $ Stuck $ R1C (Right as') (Right bs') (Right cs')
      (Polynomial as', Polynomial bs', Polynomial cs') -> return $ Stuck $ R1C (Right as') (Right bs') (Right cs')
  where
    -- return Eliminated if the equation holds
    -- else throw an error
    eliminatedIfHold :: (Num n, Eq n) => n -> n -> n -> M n (Result (R1C n))
    eliminatedIfHold a b c = do
      if a * b == c
        then return Eliminated
        else throwError $ R1CInconsistentError $ R1C (Left a) (Left b) (Left c)

-- | Substitute varaibles with values in a polynomial
substAndView :: (Num n, Eq n) => IntMap n -> Poly n -> PolyResult n
substAndView bindings xs = case Poly.substWithIntMap xs bindings of
  Left constant -> Constant constant
  Right poly ->
    let (constant, xs') = Poly.view poly
     in case IntMap.minViewWithKey xs' of
          Nothing -> Constant constant
          Just ((var, coeff), xs'') ->
            if IntMap.null xs''
              then Uninomial poly constant (var, coeff)
              else Polynomial poly

-- | View of result after substituting a polynomial
data PolyResult n
  = Constant n
  | Uninomial (Poly n) n (Var, n)
  | Polynomial (Poly n)
  deriving (Show, Eq, Ord, Functor)

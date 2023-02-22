{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Interpreter.R1CS (run, run') where

import Control.Monad.Except
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Validation (toEither)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Keelung.Compiler.Syntax.FieldBits (toBits)
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Constraint.R1C
import Keelung.Constraint.R1CS
import Keelung.Data.BinRep (BinRep (..))
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.VarGroup
import Keelung.Interpreter.Monad (Constraint (..), Error (..))
import Keelung.Syntax
import Keelung.Syntax.Counters

run :: (GaloisField n, Integral n) => R1CS n -> Inputs n -> Either (Error n) [n]
run r1cs inputs = fst <$> run' r1cs inputs

-- | Return interpreted outputs along with the witnesses
run' :: (GaloisField n, Integral n) => R1CS n -> Inputs n -> Either (Error n) ([n], Vector n)
run' r1cs inputs = do
  let constraints = fromOrdinaryConstraints r1cs

  witness <- runM inputs $ goThroughManyTimes constraints
  -- extract output values from the witness
  let (start, end) = getOutputVarRange (r1csCounters r1cs)
  let outputVars = [start .. end - 1]
  let outputs = map (witness Vector.!) outputVars

  return (outputs, witness)

-- | Return Constraints from a R1CS, which include:
--   1. ordinary constraints
--   2. Boolean input variable constraints
--   3. binary representation constraints
--   4. CNEQ constraints
fromOrdinaryConstraints :: (Num n, Eq n) => R1CS n -> Seq (Constraint n)
fromOrdinaryConstraints (R1CS ordinaryConstraints counters cneqs) =
  Seq.fromList (map R1CConstraint ordinaryConstraints)
    <> Seq.fromList booleanInputVarConstraints
    <> Seq.fromList (map BinRepConstraint (getBinReps counters))
    <> Seq.fromList (map CNEQConstraint cneqs)
  where
    booleanInputVarConstraints =
      let generate (start, end) =
            map
              ( \var ->
                  R1CConstraint $
                    R1C
                      (Right (Poly.singleVar var))
                      (Right (Poly.singleVar var))
                      (Right (Poly.singleVar var))
              )
              [start .. end - 1]
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
    Stuck _ -> throwError (R1CSStuckError $ toList constraints)

-- Go through a sequence of constraints
goThroughOnce :: (GaloisField n, Integral n) => Seq (Constraint n) -> M n (Result (Seq (Constraint n)))
goThroughOnce constraints = mconcat <$> mapM shrink (toList constraints)

lookupVar :: Var -> M n (Maybe n)
lookupVar var = gets (IntMap.lookup var)

shrink :: (GaloisField n, Integral n) => Constraint n -> M n (Result (Seq (Constraint n)))
shrink (R1CConstraint r1c) = fmap (pure . R1CConstraint) <$> shrinkR1C r1c
shrink (CNEQConstraint cneq) = fmap (pure . CNEQConstraint) <$> shrinkCNEQ cneq
shrink (BinRepConstraint binRep) = fmap (pure . BinRepConstraint) <$> shrinkBinRep binRep

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

-- if (x - y) = 0 then m = 0 else m = recip (x - y)
shrinkCNEQ :: (GaloisField n, Integral n) => CNEQ n -> M n (Result (CNEQ n))
shrinkCNEQ cneq@(CNEQ (Left x) (Left y) m) = do
  resultX <- lookupVar x
  resultY <- lookupVar y
  case (resultX, resultY) of
    (Nothing, Nothing) -> return $ Stuck cneq
    (Just a, Nothing) -> return $ Shrinked (CNEQ (Right a) (Left y) m)
    (Nothing, Just b) -> return $ Shrinked (CNEQ (Left x) (Right b) m)
    (Just a, Just b) -> shrinkCNEQ (CNEQ (Right a) (Right b) m)
shrinkCNEQ cneq@(CNEQ (Left x) (Right b) m) = do
  result <- lookupVar x
  case result of
    Nothing -> return $ Stuck cneq
    Just a -> shrinkCNEQ (CNEQ (Right a) (Right b) m)
shrinkCNEQ cneq@(CNEQ (Right a) (Left y) m) = do
  result <- lookupVar y
  case result of
    Nothing -> return $ Stuck cneq
    Just b -> shrinkCNEQ (CNEQ (Right a) (Right b) m)
shrinkCNEQ (CNEQ (Right a) (Right b) m) = do
  if a == b
    then do
      bindVar m 0
    else do
      bindVar m (recip (a - b))
  return Eliminated

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = StateT (IntMap n) (Except (Error n))

runM :: (GaloisField n, Integral n) => Inputs n -> M n a -> Either (Error n) (Vector n)
runM inputs p =
  let counters = Inputs.inputCounters inputs
   in case runExcept (execStateT p (Inputs.toIntMap inputs)) of
        Left err -> Left err
        Right bindings -> case toEither $ toTotal' (getCountBySort OfPublicInput counters + getCountBySort OfPrivateInput counters, bindings) of
          Left unbound -> Left (VarUnassignedError' unbound)
          Right bindings' -> Right bindings'

bindVar :: Var -> n -> M n ()
bindVar var val = modify' $ IntMap.insert var val

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
    R1C (Left _) (Left _) (Left _) -> return Eliminated
    R1C (Left a) (Left b) (Right cs) -> case substAndView bindings cs of
      Constant _ -> return Eliminated
      Uninomial c (var, coeff) -> do
        -- a * b - c = coeff var
        bindVar var ((a * b - c) / coeff)
        return Eliminated
      Polynomial _ -> return $ Stuck r1c
    R1C (Left a) (Right bs) (Left c) -> case substAndView bindings bs of
      Constant _ -> return Eliminated
      Uninomial b (var, coeff) -> do
        if a == 0
          then return Eliminated
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
      Polynomial _ -> return $ Stuck r1c
    R1C (Left a) (Right bs) (Right cs) -> case (substAndView bindings bs, substAndView bindings cs) of
      (Constant _, Constant _) -> return Eliminated
      (Constant b, Uninomial c (var, coeff)) -> do
        -- a * b - c = coeff var
        bindVar var ((a * b - c) / coeff)
        return Eliminated
      (Constant _, Polynomial _) -> return $ Stuck r1c
      (Uninomial b (var, coeff), Constant c) ->
        if a == 0
          then return Eliminated
          else do
            -- a * (b + coeff var) = c
            bindVar var ((c - a * b) / (coeff * a))
            return Eliminated
      (Uninomial _ _, Uninomial _ _) -> return $ Stuck r1c
      (Uninomial _ _, Polynomial _) -> return $ Stuck r1c
      (Polynomial _, Constant _) -> return $ Stuck r1c
      (Polynomial _, Uninomial _ _) -> return $ Stuck r1c
      (Polynomial _, Polynomial _) -> return $ Stuck r1c
    R1C (Right as) (Left b) (Left c) -> case substAndView bindings as of
      Constant _ -> return Eliminated
      Uninomial a (var, coeff) -> do
        if b == 0
          then return Eliminated
          else do
            -- (a + coeff var) * b = c
            -- var = (c - a * b) / (coeff * b)
            bindVar var ((c - a * b) / (coeff * b))
            return Eliminated
      Polynomial _ -> return $ Stuck r1c
    R1C (Right as) (Left b) (Right cs) -> case (substAndView bindings as, substAndView bindings cs) of
      (Constant _, Constant _) -> return Eliminated
      (Constant a, Uninomial c (var, coeff)) -> do
        -- a * b - c = coeff var
        bindVar var ((a * b - c) / coeff)
        return Eliminated
      (Constant _, Polynomial _) -> return $ Stuck r1c
      (Uninomial a (var, coeff), Constant c) -> do
        if b == 0
          then return Eliminated
          else do
            -- (a + coeff var) * b = c
            bindVar var ((c - a * b) / (coeff * b))
            return Eliminated
      (Uninomial _ _, Uninomial _ _) -> return $ Stuck r1c
      (Uninomial _ _, Polynomial _) -> return $ Stuck r1c
      (Polynomial _, Constant _) -> return $ Stuck r1c
      (Polynomial _, Uninomial _ _) -> return $ Stuck r1c
      (Polynomial _, Polynomial _) -> return $ Stuck r1c
    R1C (Right as) (Right bs) (Left c) -> case (substAndView bindings as, substAndView bindings bs) of
      (Constant _, Constant _) -> return Eliminated
      (Constant a, Uninomial b (var, coeff)) -> do
        if a == 0
          then return Eliminated
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
      (Constant _, Polynomial _) -> return $ Stuck r1c
      (Uninomial a (var, coeff), Constant b) -> do
        if b == 0
          then return Eliminated
          else do
            -- (a + coeff var) * b = c
            bindVar var ((c - a * b) / (coeff * b))
            return Eliminated
      (Uninomial _ _, Uninomial _ _) -> return $ Stuck r1c
      (Uninomial _ _, Polynomial _) -> return $ Stuck r1c
      (Polynomial _, Constant _) -> return $ Stuck r1c
      (Polynomial _, Uninomial _ _) -> return $ Stuck r1c
      (Polynomial _, Polynomial _) -> return $ Stuck r1c
    R1C (Right as) (Right bs) (Right cs) -> case (substAndView bindings as, substAndView bindings bs, substAndView bindings cs) of
      (Constant _, Constant _, Constant _) -> return Eliminated
      (Constant a, Constant b, Uninomial c (var, coeff)) -> do
        -- a * b - c = coeff var
        bindVar var ((a * b - c) / coeff)
        return Eliminated
      (Constant _, Constant _, Polynomial _) -> return $ Stuck r1c
      (Constant a, Uninomial b (var, coeff), Constant c) -> do
        if a == 0
          then return Eliminated
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
      (Constant _, Uninomial _ _, Uninomial _ _) -> return $ Stuck r1c
      (Constant _, Uninomial _ _, Polynomial _) -> return $ Stuck r1c
      (Constant _, Polynomial _, Constant _) -> return $ Stuck r1c
      (Constant _, Polynomial _, Uninomial _ _) -> return $ Stuck r1c
      (Constant _, Polynomial _, Polynomial _) -> return $ Stuck r1c
      (Uninomial a (var, coeff), Constant b, Constant c) -> do
        if b == 0
          then return Eliminated
          else do
            -- (a + coeff var) * b = c
            bindVar var ((c - a * b) / (coeff * b))
            return Eliminated
      (Uninomial _ _, Constant _, Uninomial _ _) -> return $ Stuck r1c
      (Uninomial _ _, Constant _, Polynomial _) -> return $ Stuck r1c
      (Uninomial _ _, Uninomial _ _, Constant _) -> return $ Stuck r1c
      (Uninomial _ _, Uninomial _ _, Uninomial _ _) -> return $ Stuck r1c
      (Uninomial _ _, Uninomial _ _, Polynomial _) -> return $ Stuck r1c
      (Uninomial _ _, Polynomial _, Constant _) -> return $ Stuck r1c
      (Uninomial _ _, Polynomial _, Uninomial _ _) -> return $ Stuck r1c
      (Uninomial _ _, Polynomial _, Polynomial _) -> return $ Stuck r1c
      (Polynomial _, Constant _, Constant _) -> return $ Stuck r1c
      (Polynomial _, Constant _, Uninomial _ _) -> return $ Stuck r1c
      (Polynomial _, Constant _, Polynomial _) -> return $ Stuck r1c
      (Polynomial _, Uninomial _ _, Constant _) -> return $ Stuck r1c
      (Polynomial _, Uninomial _ _, Uninomial _ _) -> return $ Stuck r1c
      (Polynomial _, Uninomial _ _, Polynomial _) -> return $ Stuck r1c
      (Polynomial _, Polynomial _, Constant _) -> return $ Stuck r1c
      (Polynomial _, Polynomial _, Uninomial _ _) -> return $ Stuck r1c
      (Polynomial _, Polynomial _, Polynomial _) -> return $ Stuck r1c

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
              then Uninomial constant (var, coeff)
              else Polynomial poly

-- | View of result after substituting a polynomial
data PolyResult n
  = Constant n
  | Uninomial n (Var, n)
  | Polynomial (Poly n)

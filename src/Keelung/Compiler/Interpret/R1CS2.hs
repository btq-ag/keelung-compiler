{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Interpret.R1CS2 (run, run') where

import Control.Monad.Except
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Validation (toEither)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Keelung.Compiler.Interpret.Monad (Error (..))
import Keelung.Compiler.Syntax.Inputs (Inputs)
import qualified Keelung.Compiler.Syntax.Inputs as Inputs
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Constraint.R1C
import Keelung.Constraint.R1CS
import Keelung.Data.Bindings
import Keelung.Syntax.Counters
import Keelung.Types

run :: (GaloisField n, Integral n) => R1CS n -> Inputs n -> Either (Error n) [n]
run r1cs inputs = fst <$> run' r1cs inputs

-- | Return interpreted outputs along with the witnesses
run' :: (GaloisField n, Integral n) => R1CS n -> Inputs n -> Either (Error n) ([n], Vector n)
run' r1cs inputs = do
  witness <- runM inputs $ goThrough (Set.fromList (toR1Cs r1cs))
  -- extract output values from the witness
  let (start, end) = getOutputVarRange (r1csCounters r1cs)
  let outputVars = [start .. end - 1]
  let outputs = map (witness Vector.!) outputVars

  return (outputs, witness)

-- Go through a set of constraints and return the one constraint that cannot be shrinked or eliminated
goThrough :: (GaloisField n, Integral n) => Set (R1C n) -> M n ()
goThrough set = case Set.minView set of
  Nothing -> return ()
  Just (r1c, set') -> do
    result <- shrink r1c
    case result of
      Shrinked r1c' -> goThrough (Set.insert r1c' set')
      Eliminated -> goThrough set'
      Stuck -> throwError $ R1CSStuckError r1c

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = StateT (IntMap n) (Except (Error n))

runM :: Num n => Inputs n -> M n a -> Either (Error n) (Vector n)
runM inputs p =
  let counters = Inputs.varCounters inputs
   in case runExcept (execStateT p (Inputs.toIntMap inputs)) of
        Left err -> Left err
        Right bindings -> case toEither $ toTotal' (getCountBySort OfInput counters, bindings) of
          Left unbound -> Left (VarUnassignedError' unbound)
          Right bindings' -> Right bindings'

bindVar :: Var -> n -> M n ()
bindVar var val = modify' $ IntMap.insert var val

--------------------------------------------------------------------------------

-- | Result of shrinking a constraint
data Result n = Shrinked (R1C n) | Eliminated | Stuck

shrink :: (GaloisField n, Integral n) => R1C n -> M n (Result n)
shrink r1cs = do
  bindings <- get
  case r1cs of
    R1C (Left _) (Left _) (Left _) -> return Eliminated
    R1C (Left a) (Left b) (Right cs) -> case substAndView bindings cs of
      Constant _ -> return Eliminated
      Uninomial c (var, coeff) -> do
        -- a * b - c = coeff var
        bindVar var ((a * b - c) / coeff)
        return Eliminated
      Polynomial _ -> return Stuck
    R1C (Left a) (Right bs) (Left c) -> case substAndView bindings bs of
      Constant _ -> return Eliminated
      Uninomial b (var, coeff) -> do
        -- a * (b - coeff var) = c
        bindVar var ((b - c / a) / coeff)
        return Eliminated
      Polynomial _ -> return Stuck
    R1C (Left a) (Right bs) (Right cs) -> case (substAndView bindings bs, substAndView bindings cs) of
      (Constant _, Constant _) -> return Eliminated
      (Constant b, Uninomial c (var, coeff)) -> do
        -- a * b - c = coeff var
        bindVar var ((a * b - c) / coeff)
        return Eliminated
      (Constant _, Polynomial _) -> return Stuck
      (Uninomial b (var, coeff), Constant c) -> do
        -- a * (b + coeff var) = c
        bindVar var ((c - a * b) / (coeff * a))
        return Eliminated
      (Uninomial _ _, Uninomial _ _) -> return Stuck
      (Uninomial _ _, Polynomial _) -> return Stuck
      (Polynomial _, Constant _) -> return Stuck
      (Polynomial _, Uninomial _ _) -> return Stuck
      (Polynomial _, Polynomial _) -> return Stuck
    R1C (Right as) (Left b) (Left c) -> case substAndView bindings as of
      Constant _ -> return Eliminated
      Uninomial a (var, coeff) -> do
        -- (a + coeff var) * b = c
        -- var = (c - a * b) / (coeff * b)
        bindVar var ((c - a * b) / (coeff * b))
        return Eliminated
      Polynomial _ -> return Stuck
    R1C (Right as) (Left b) (Right cs) -> case (substAndView bindings as, substAndView bindings cs) of
      (Constant _, Constant _) -> return Eliminated
      (Constant a, Uninomial c (var, coeff)) -> do
        -- a * b - c = coeff var
        bindVar var ((a * b - c) / coeff)
        return Eliminated
      (Constant _, Polynomial _) -> return Stuck
      (Uninomial a (var, coeff), Constant c) -> do
        -- (a + coeff var) * b = c
        bindVar var ((c - a * b) / (coeff * b))
        return Eliminated
      (Uninomial _ _, Uninomial _ _) -> return Stuck
      (Uninomial _ _, Polynomial _) -> return Stuck
      (Polynomial _, Constant _) -> return Stuck
      (Polynomial _, Uninomial _ _) -> return Stuck
      (Polynomial _, Polynomial _) -> return Stuck
    R1C (Right as) (Right bs) (Left c) -> case (substAndView bindings as, substAndView bindings bs) of
      (Constant _, Constant _) -> return Eliminated
      (Constant a, Uninomial b (var, coeff)) -> do
        -- a * (b + coeff var) = c
        bindVar var ((c / a - b) / coeff)
        return Eliminated
      (Constant _, Polynomial _) -> return Stuck
      (Uninomial a (var, coeff), Constant b) -> do
        -- (a + coeff var) * b = c
        bindVar var ((c - a * b) / (coeff * b))
        return Eliminated
      (Uninomial _ _, Uninomial _ _) -> return Stuck
      (Uninomial _ _, Polynomial _) -> return Stuck
      (Polynomial _, Constant _) -> return Stuck
      (Polynomial _, Uninomial _ _) -> return Stuck
      (Polynomial _, Polynomial _) -> return Stuck
    R1C (Right as) (Right bs) (Right cs) -> case (substAndView bindings as, substAndView bindings bs, substAndView bindings cs) of
      (Constant _, Constant _, Constant _) -> return Eliminated
      (Constant a, Constant b, Uninomial c (var, coeff)) -> do
        -- a * b - c = coeff var
        bindVar var ((a * b - c) / coeff)
        return Eliminated
      (Constant _, Constant _, Polynomial _) -> return Stuck
      (Constant a, Uninomial b (var, coeff), Constant c) -> do
        -- a * (b + coeff var) = c
        bindVar var ((c / a - b) / coeff)
        return Eliminated
      (Constant _, Uninomial _ _, Uninomial _ _) -> return Stuck
      (Constant _, Uninomial _ _, Polynomial _) -> return Stuck
      (Constant _, Polynomial _, Constant _) -> return Stuck
      (Constant _, Polynomial _, Uninomial _ _) -> return Stuck
      (Constant _, Polynomial _, Polynomial _) -> return Stuck
      (Uninomial a (var, coeff), Constant b, Constant c) -> do
        -- (a + coeff var) * b = c
        bindVar var ((c - a * b) / (coeff * b))
        return Eliminated
      (Uninomial _ _, Constant _, Uninomial _ _) -> return Stuck
      (Uninomial _ _, Constant _, Polynomial _) -> return Stuck
      (Uninomial _ _, Uninomial _ _, Constant _) -> return Stuck
      (Uninomial _ _, Uninomial _ _, Uninomial _ _) -> return Stuck
      (Uninomial _ _, Uninomial _ _, Polynomial _) -> return Stuck
      (Uninomial _ _, Polynomial _, Constant _) -> return Stuck
      (Uninomial _ _, Polynomial _, Uninomial _ _) -> return Stuck
      (Uninomial _ _, Polynomial _, Polynomial _) -> return Stuck
      (Polynomial _, Constant _, Constant _) -> return Stuck
      (Polynomial _, Constant _, Uninomial _ _) -> return Stuck
      (Polynomial _, Constant _, Polynomial _) -> return Stuck
      (Polynomial _, Uninomial _ _, Constant _) -> return Stuck
      (Polynomial _, Uninomial _ _, Uninomial _ _) -> return Stuck
      (Polynomial _, Uninomial _ _, Polynomial _) -> return Stuck
      (Polynomial _, Polynomial _, Constant _) -> return Stuck
      (Polynomial _, Polynomial _, Uninomial _ _) -> return Stuck
      (Polynomial _, Polynomial _, Polynomial _) -> return Stuck

-- | Substitute variables with values in a polynomial
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

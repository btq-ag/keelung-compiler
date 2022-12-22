-- Interpreter for Keelung.Compiler.R1CS
module Keelung.Compiler.Interpret.R1CS (run, run', runNew) where

import Control.Monad.Except
import Control.Monad.State
import qualified Data.Either as Either
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Keelung.Compiler.R1CS (ExecError (..), witnessOfR1CS)
import Keelung.Compiler.Syntax.Inputs (Inputs)
import qualified Keelung.Compiler.Syntax.Inputs as Inputs
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Constraint.R1C
import Keelung.Constraint.R1CS
import Keelung.Syntax.Counters
import Keelung.Types

run :: (GaloisField n, Integral n) => R1CS n -> Inputs n -> Either (ExecError n) [n]
run r1cs inputs = fst <$> run' r1cs inputs

-- | Return interpreted outputs along with the witnesses
run' :: (GaloisField n, Integral n) => R1CS n -> Inputs n -> Either (ExecError n) ([n], IntMap n)
run' r1cs inputs = do
  witness <- witnessOfR1CS inputs r1cs
  let (start, end) = getOutputVarRange (r1csCounters r1cs)
  let outputVars = [start .. end - 1]
  -- extract output values from the witness
  let (execErrors, outputs) =
        Either.partitionEithers $
          map
            ( \var ->
                case IntMap.lookup var witness of
                  Nothing -> Left var
                  Just value -> Right value
            )
            outputVars

  unless (null execErrors) $ do
    Left $ ExecOutputVarsNotMappedError outputVars witness

  return (outputs, witness)

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = State (Vector (Maybe n))

runM :: Num n => Inputs n -> M n a -> Vector n
runM inputs p =
  let vector = execState p (Inputs.toVector inputs)
   in Vector.imapMaybe
        ( \i x -> case x of
            Nothing -> error $ "[ panic ] R1CS interpreter: variable $" ++ show i ++ " not assigned with value"
            Just val -> Just val
        )
        vector

-- lookupVar :: Show n => Var -> M n n
-- lookupVar var = do
--   env <- get
--   case env Vector.!? var of
--     Nothing -> error "[ panic ] R1CS interpreter: variable out of range"
--     Just Nothing -> error "[ panic ] R1CS interpreter: variable not assigned with value"
--     Just (Just value) -> return value

bindVar :: Var -> n -> M n ()
bindVar var val = do
  env <- get
  put $ env Vector.// [(var, Just val)]

runNew :: (GaloisField n, Integral n) => R1CS n -> Inputs n -> Vector n
runNew r1cs inputs = runM inputs $ do
  result <- goThrough (Set.fromList (toR1Cs r1cs))
  case result of
    Nothing -> return ()
    Just r1c -> error $ "[ panic ] R1CS interpreter: stuck at " ++ show r1c
  where
    -- Go through a set of constraints and return the one constraint that cannot be shrinked or eliminated
    goThrough :: (GaloisField n, Integral n) => Set (R1C n) -> M n (Maybe (R1C n))
    goThrough set = case Set.minView set of
      Nothing -> return Nothing
      Just (r1c, set') -> do
        result <- shrink r1c
        case result of
          Shrinked r1c' -> goThrough (Set.insert r1c' set')
          Eliminated -> goThrough set'
          Stuck -> return $ Just r1c

--------------------------------------------------------------------------------

-- | Result of shrinking a constraint
data Result n = Shrinked (R1C n) | Eliminated | Stuck

shrink :: (GaloisField n, Integral n) => R1C n -> M n (Result n)
shrink r1cs = do
  env <- get
  case r1cs of
    R1C (Left _) (Left _) (Left _) -> return Eliminated
    R1C (Left a) (Left b) (Right cs) -> case substAndView env cs of
      Constant _ -> return Eliminated
      Uninomial c (var, coeff) -> do
        -- a * b - c = coeff var
        bindVar var ((a * b - c) / coeff)
        return Eliminated
      Polynomial _ -> return Stuck
    R1C (Left a) (Right bs) (Left c) -> case substAndView env bs of
      Constant _ -> return Eliminated
      Uninomial b (var, coeff) -> do
        -- a * (b - coeff var) = c
        bindVar var ((b - c / a) / coeff)
        return Eliminated
      Polynomial _ -> return Stuck
    R1C (Left a) (Right bs) (Right cs) -> case (substAndView env bs, substAndView env cs) of
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
    R1C (Right as) (Left b) (Left c) -> case substAndView env as of
      Constant _ -> return Eliminated
      Uninomial a (var, coeff) -> do
        -- (a + coeff var) * b = c
        -- var = (c - a * b) / (coeff * b)
        bindVar var ((c - a * b) / (coeff * b))
        return Eliminated
      Polynomial _ -> return Stuck
    R1C (Right as) (Left b) (Right cs) -> case (substAndView env as, substAndView env cs) of
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
    R1C (Right as) (Right bs) (Left c) -> case (substAndView env as, substAndView env bs) of
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
    R1C (Right as) (Right bs) (Right cs) -> case (substAndView env as, substAndView env bs, substAndView env cs) of
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
substAndView :: (Num n, Eq n) => Vector (Maybe n) -> Poly n -> PolyResult n
substAndView env xs = case Poly.substWithVector xs env of
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

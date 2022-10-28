-- Interpreter for Keelung.Compiler.R1CS
module Keelung.Compiler.Interpret.R1CS (run, run') where

import Control.Monad.Except
import qualified Data.Either as Either
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Keelung.Compiler.R1CS (ExecError (..), witnessOfR1CS)
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Constraint.R1CS
import Keelung.Syntax.VarCounters

run :: (GaloisField n, Integral n) => R1CS n -> Inputs n -> Either (ExecError n) [n]
run r1cs inputs = fst <$> run' r1cs inputs

-- | Return interpreted outputs along with the witnesses
run' :: (GaloisField n, Integral n) => R1CS n -> Inputs n -> Either (ExecError n) ([n], IntMap n)
run' r1cs inputs = do
  witness <- witnessOfR1CS inputs r1cs
  let varCounters = r1csVarCounters r1cs
  -- extract output values from the witness
  let (execErrors, outputs) =
        Either.partitionEithers $
          map
            ( \var ->
                case IntMap.lookup var witness of
                  Nothing -> Left var
                  Just value -> Right value
            )
            (outputVars varCounters)

  unless (null execErrors) $ do
    Left $ ExecOutputVarsNotMappedError (outputVars varCounters) witness

  return (outputs, witness)

-- -- | Return interpreted outputs along with the witnesses
-- run2 :: (GaloisField n, Integral n) => R1CS n -> [n] -> Either (ExecError n) ([n], Witness n)
-- run2 r1cs inputs = runM inputs $ do
--   let constraints = toR1Cs r1cs

--   return undefined

-- -- -- | Go through a set of constraints and return the one constraint that cannot be shrinked or eliminated
-- -- goThrough :: (GaloisField n, Integral n) => Set (R1C n) -> M n (Maybe (R1C n))
-- -- goThrough set = case Set.minView set of
-- --   Nothing -> return Nothing
-- --   Just (r1c, set') -> do
-- --     result <- shrink r1c
-- --     case result of
-- --       Shrinked r1c' -> goThrough (Set.insert r1c' set')
-- --       Eliminated -> goThrough set'
-- --       Stuck -> return $ Just r1c

-- shrink :: (GaloisField n, Integral n) => R1C n -> M n (Result n)
-- shrink (R1C a b c) = do
--   env <- get

--   case (substAndView env a, substAndView env b, substAndView env c) of
--     (Left _, Left _, Left _) -> return Eliminated
--     (Left ac, Left bc, Right (cc, () cs)) -> case IntMap.toList cs of
--       [] ->

--        _ -- ac * bc - cc = cs
--     (Left ac, Right (bc, bs), Left cc) -> _
--     (Left ac, Right (bc, bs), Right (cc, cs)) -> _
--     (Right (ac, as), y, z) -> _

-- substAndView :: (Num n, Eq n) => IntMap n -> Either n (Poly n) -> Either n (n, (Var, n), IntMap n)
-- substAndView _ (Left constant) = Left constant
-- substAndView bindings (Right xs) =
--   let (constant, xs') = Poly.view (Poly.substWithBindings xs bindings)
--    in case IntMap.minViewWithKey xs' of
--         Nothing -> Left constant
--         Just ((var, coeff), xs'') -> Right (constant, (var, coeff), xs'')

-- -- | Result of shrinking a constraint
-- data Result n = Shrinked (R1C n) | Eliminated | Stuck

-- -- Nothing -> return set
-- -- Just (r1c, set') -> do
-- --   let (a, b, c) = r1c
-- --   a' <- goThroughVars a
-- --   b' <- goThroughVars b
-- --   c' <- goThroughVars c
-- --   let r1c' = (a', b', c')
-- --   goThroughConstraints $ Set.insert r1c' set'

-- --------------------------------------------------------------------------------

-- -- | The interpreter monad
-- type M n = StateT (IntMap n) (Except (ExecError n))

-- runM :: [n] -> M n a -> Either (ExecError n) (a, Witness n)
-- runM inputs p = runExcept (runStateT p inputBindings)
--   where
--     inputBindings = IntMap.fromDistinctAscList $ zip [0 ..] inputs

-- lookupVar :: Show n => Int -> M n n
-- lookupVar var = do
--   bindings <- get
--   case IntMap.lookup var bindings of
--     Nothing -> throwError $ ExecVarUnassignedError [var] bindings
--     Just val -> return val

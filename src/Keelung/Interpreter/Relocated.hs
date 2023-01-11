-- Interpreter for Keelung.Compiler.R1CS
module Keelung.Interpreter.Relocated (run, run') where

import Control.Monad.Except
import qualified Data.Either as Either
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Keelung.Compiler.R1CS (ExecError (..), witnessOfR1CS)
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Constraint.R1CS
import Keelung.Syntax.Counters

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

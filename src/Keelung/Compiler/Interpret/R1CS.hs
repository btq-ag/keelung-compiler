-- Interpreter for Keelung.Compiler.R1CS
module Keelung.Compiler.Interpret.R1CS (run) where

import Control.Monad (unless)
import qualified Data.Either as Either
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap as IntMap
import Keelung.Compiler.R1CS (ExecError (..), witnessOfR1CS)
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Types

run :: (GaloisField n, Integral n) => R1CS n -> [n] -> Either (ExecError n) [n]
run r1cs inputs = do
  witness <- witnessOfR1CS inputs r1cs
  let varCounters = r1csVarCounters r1cs
  -- extract output values from the witness
  let outputVars = [varInput varCounters .. varInput varCounters + varOutput varCounters - 1]

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

  return outputs
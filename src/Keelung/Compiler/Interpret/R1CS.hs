-- Interpreter for Keelung.Compiler.R1CS
module Keelung.Compiler.Interpret.R1CS (run) where

import Control.Monad (unless)
import qualified Data.Either as Either
import Data.Field.Galois (GaloisField)
import qualified Data.IntMap as IntMap
import Keelung.Compiler.R1CS (ExecError (..), witnessOfR1CS)
import Keelung.Constraint.R1CS (R1CS (..))

run :: (GaloisField n, Integral n) => R1CS n -> [n] -> Either (ExecError n) [n]
run r1cs inputs = do
  witness <- witnessOfR1CS inputs r1cs
  -- extract output values from the witness
  let outputVars = [ r1csInputVarSize r1cs .. r1csInputVarSize r1cs + r1csOutputVarSize r1cs - 1]

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

-- --------------------------------------------------------------------------------

-- data InterpretError n
--   = InterpretUnboundVarError Var (IntMap n)
--   | InterpretUnboundAddrError Addr Heap
--   | InterpretAssertionError (Boolean) (IntMap n)
--   deriving (Eq)

-- instance (GaloisField n, Integral n) => Show (InterpretError n) where
--   show (InterpretUnboundVarError var bindings) =
--     "unbound variable " ++ show var
--       ++ " in bindings "
--       ++ show (fmap N bindings)
--   show (InterpretUnboundAddrError var heap) =
--     "unbound address " ++ show var
--       ++ " in heap "
--       ++ show heap
--   show (InterpretAssertionError val bindings) =
--     "assertion failed: " ++ show val
--       ++ "\nbindings of variables: "
--       ++ show (fmap N bindings)

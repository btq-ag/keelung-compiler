{-# LANGUAGE GADTs #-}

module Benchmark.Snarkl where

import Data.Foldable (toList)
import qualified Data.IntMap.Lazy as IntMap
import qualified Data.Set as Set
import Data.Typeable
import GHC.IO.Exception
import Snarkl hiding (return)
import Snarkl.Serialize (Serialize)
import Snarkl.Compile (eraseType)
import Snarkl.Expr (Exp(..))

-- Just elaborate to TExp.
benchElaborate :: Typeable ty => Comp ty a -> Int
benchElaborate = extract_rat . lastSeq . elabTExp . elaborate
  where
    extract_rat :: TExp ty a -> Int
    extract_rat te = case te of
      TEVar _ -> 0
      TEVal _ -> 1
      TEUnop _ _ -> 2
      TEBinop {} -> 3
      TEIf {} -> 4
      TEAssert _ _ -> 5
      TESeq _ _ -> 6
      TEBot -> 7

-- Just elaborate to TExp.
benchEraseType :: (Typeable ty, GaloisField a) => Comp ty a -> Int
benchEraseType = extract_rat . eraseType . lastSeq . elabTExp . elaborate
  where
    extract_rat :: Exp a -> Int
    extract_rat te = case te of
      EVar _ -> 0
      EVal _ -> 1
      EUnop _ _ -> 2
      EBinop _ _ -> 3
      EIf {} -> 4
      EAssert _ _ -> 5
      ESeq _ -> 6
      EUnit -> 7

-- Just compile to constraints (no simplification yet).
benchCompile :: (Typeable ty, GaloisField a, Serialize a) => Comp ty a -> IO [String]
benchCompile prog = do
  let constraints =
        cs_constraints $
          compile $
            Snarkl.elaborate prog
  putStrLn $ "Number of constraints: " ++ show (Set.size constraints)
  return $ map serialize $ toList constraints

-- Compile to constraints and simplify.
benchSimplify :: (Typeable ty, GaloisField a, Serialize a) => Comp ty a -> [String]
benchSimplify =
  map serialize . toList . cs_constraints . snd
    . simplifyConstrantSystem False IntMap.empty
    . compile
    . Snarkl.elaborate

-- Same as 'r1cs', but also generates and serializes
-- a satisfying assignment, as well as serializing the given inputs.
witgen ::
  (Typeable ty, Serialize a, GaloisField a, Bounded a, Integral a) => SimplParam -> Comp ty a -> [a] -> String
witgen flag prog inputs = serializeInputs inputs (compileToR1CS flag prog)

-- Run libsnark on the resulting files.
crypto :: (Typeable ty, Serialize a, GaloisField a, Bounded a, Integral a) => SimplParam -> Comp ty a -> [a] -> IO ()
crypto simpl mf inputs = do
  exit <- snarkify "test" simpl mf inputs
  case exit of
    ExitSuccess -> return ()
    ExitFailure err ->
      fail_with $ ErrMsg $ "full failed with " ++ show err

-- This function "executes" the comp two ways, once by interpreting
-- the resulting TExp and second by interpreting the resulting circuit
-- on the inputs provided. Both results are checked to match 'res'.
-- The function outputs a 'Result' that details number of variables and
-- constraints in the resulting constraint system.
compareWithResult ::
  (Typeable ty, GaloisField a, Serialize a, Bounded a, Integral a) => SimplParam -> Comp ty a -> [a] -> a -> Bool
compareWithResult flag prog inputs output =
  let result = execute flag prog inputs
   in resultResult result == output

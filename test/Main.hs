{-# LANGUAGE DataKinds #-}

module Main where

import qualified AggregateSignature.Program.Snarkl as Snarkl
-- import qualified AggregateSignature.Program.Keelung as Keelung
import AggregateSignature.Util
import Keelung
import qualified Snarkl
import Test.Hspec


-- runGF64 :: Snarkl.Comp ty GF64 -> [GF64] -> GF64
-- runGF64 mf args = Snarkl.resultResult $ Snarkl.execute simpl mf args

-- runGF181 :: SimplParam -> Snarkl.Comp ty GF181 -> [GF181] -> GF181
-- runGF181 simpl mf args = Snarkl.resultResult $ Snarkl.execute simpl mf args

-- runKeelungGF181 :: SimplParam -> Keelung.Comp ty GF181 -> [GF181] -> Maybe GF181
-- runKeelungGF181 mode prog args = either (const Nothing) Just $ Snarkl.resultResult <$> Keelung.execute mode prog args

-- | (1) Compile to R1CS.
--   (2) Generate a satisfying assignment, 'w'.
--   (3) Check whether 'w' satisfies the constraint system produced in (1).
--   (4) Check whether the R1CS result matches the interpreter result.
--   (5) Return the 'Result'.
-- execute :: (GaloisField n, Bounded n, Integral n) => Comp ty n -> [n] -> Either String () 
-- execute prog inputs = do
--   r1cs <- compile prog

--   let outputVar = r1csOutputVar r1cs 
--   let numberOfVars = r1csNumVars r1cs 
--   let clauses = r1csClauses r1cs
--   let witness = witnessOfR1CS inputs r1cs

--   return ()



  --     ng = length (Snarkl.r1csClauses r1cs)
  --     wit = Snarkl.wit_of_r1cs inputs r1cs

  -- out <- case IntMap.lookup out_var wit of
  --   Nothing ->
  --     throwError $
  --       ErrMsg
  --         ( "output variable "
  --             ++ show out_var
  --             ++ "not mapped, in\n  "
  --             ++ show wit
  --         )
  --   Just out_val -> return out_val
  -- -- Interpret the program using the executable semantics and
  -- -- the input assignment (a subset of 'wit').
  -- -- Output the return value of 'e'.
  -- out_interp <- interpret prog inputs

  -- result <-
  --   if out_interp == out
  --     then return $ Snarkl.satisfyR1CS wit r1cs
  --     else
  --       throwError $
  --         ErrMsg $
  --           "interpreter result "
  --             ++ show out_interp
  --             ++ " differs from actual result "
  --             ++ show out

  -- return $ Result result nw ng out r1cs



runSnarklAggSig :: Int -> Int -> GF181
runSnarklAggSig dimension numberOfSignatures =
  let settings =
        Settings
          { enableAggSigChecking = True,
            enableBitStringSizeChecking = True,
            enableBitStringValueChecking = True,
            enableSigSquareChecking = True,
            enableSigLengthChecking = True
          }
      setup = makeSetup dimension numberOfSignatures 42 settings :: Setup GF181
   in Snarkl.resultResult $
        Snarkl.execute
          Snarkl.Simplify
          (Snarkl.aggregateSignature setup :: Snarkl.Comp 'Snarkl.TBool GF181)
          (genInputFromSetup setup)

-- runKeelungAggSig :: Int -> Int -> Maybe GF181
-- runKeelungAggSig dimension numberOfSignatures =
--   let settings =
--         Settings
--           { enableAggSigChecking = True,
--             enableBitStringSizeChecking = True,
--             enableBitStringValueChecking = True,
--             enableSigSquareChecking = True,
--             enableSigLengthChecking = True
--           }
--       setup = makeSetup dimension numberOfSignatures 42 settings :: Setup GF181
--    in either (const Nothing) Just $
--         Snarkl.resultResult
--           <$> Keelung.execute
--             Simplify
--             (Keelung.aggregateSignature setup :: Comp 'Bool GF181)
--             (genInputFromSetup setup)

main :: IO ()
main = hspec $ do
  describe "Aggregate Signature" $ do
    describe "Snarkl" $ do
      it "dim:1 sig:1" $
        runSnarklAggSig 1 1 `shouldBe` 1
      it "dim:1 sig:10" $
        runSnarklAggSig 1 10 `shouldBe` 1
      it "dim:10 sig:1" $
        runSnarklAggSig 10 1 `shouldBe` 1
      it "dim:10 sig:10" $
        runSnarklAggSig 10 10 `shouldBe` 1
    -- describe "Keelung" $ do
    --   it "dim:1 sig:1" $
    --     runKeelungAggSig 1 1 `shouldBe` Just 1
    --   it "dim:1 sig:10" $
    --     runKeelungAggSig 1 10 `shouldBe` Just 1
    --   it "dim:10 sig:1" $
    --     runKeelungAggSig 10 1 `shouldBe` Just 1
    --   it "dim:10 sig:10" $
    --     runKeelungAggSig 10 10 `shouldBe` Just 1
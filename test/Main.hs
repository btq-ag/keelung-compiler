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
--             (Keelung.aggregateSignature setup :: Comp GF181 'Bool)
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
{-# LANGUAGE LambdaCase #-}

module Test.Snarkjs (tests, run, testQuad) where

-- import Test.HUnit (assertFailure)

import Data.Either
import GHC.IO.Exception (ExitCode (..))
import Keelung
import Quad
import System.Process
import Test.Hspec
import Test.QuickCheck
import Test.Compilation.Util

run :: IO ()
run = hspec testQuad

-- execute :: Encode t => Comp t -> IO Counters
-- execute program = do
--   compile bn128 program >>= \case
--     Left err -> assertFailure $ show err
--     Right r1cs -> return $ r1csCounters r1cs

-- For testing with an Keelung program, given public and private inputs.
testWith :: Encode t => String -> Comp t -> [Integer] -> [Integer] -> [Integer] -> SpecWith ()
testWith name prog pubIn prvIn expected = do
  -- Testing from command line
  -- describe ("Checking if " <> name <> " compiles:") $ do
  --   it ("Compiling " <> name <> "...") $ do
  --     compile bn128 prog >>= flip shouldSatisfy isRight
  --   it "Generating Snarkjs\' binary R1CS file (.r1cs)..." $ do
  --     genCircuitBin (name <> ".r1cs") bn128 prog >>= flip shouldSatisfy isRight
  --   it "Generating Snarkjs\' binary witness file (.wtns)..." $ do
  --     genWtns (name <> ".wtns") bn128 prog pubIn prvIn >>= flip shouldSatisfy isRight
  describe "Testing Program" $ do
    it ("Testing R1CS and witness generation of " <> name) $ do
      runAll gf181 prog pubIn prvIn expected
  -- describe ("Checking " <> name <> " works with Snarkjs...") $ do
  --   it "Checking the R1CS file is accepted by Snarkjs..." $ do
  --     system ("snarkjs r1cs info " <> name <> ".r1cs") >>= shouldBe ExitSuccess
  --   it "Checking Snarkjs matches the witness with R1CS..." $ do
  --     system ("snarkjs wtns check " <> name <> ".r1cs " <> name <> ".wtns") >>= shouldBe ExitSuccess
  --     -- // Assume pot12_final.ptau is present.
  --     -- it "Preparing powers of tau with Snarkjs..." $ do
  --     --   system "snarkjs powersoftau new bn128 12 pot12.ptau" >>= shouldBe ExitSuccess
  --     --   readCreateProcessWithExitCode
  --     --     (shell "snarkjs powersoftau contribute pot12.ptau pot12_temp.ptau --name=\"First contribution\"") "123\n"
  --     --       >>= \(e, _, _) -> e `shouldBe` ExitSuccess
  --     --   system "snarkjs powersoftau beacon pot12_temp.ptau pot12_beacon.ptau 0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f 10"
  --     --     >>= shouldBe ExitSuccess
  --     --   system "snarkjs powersoftau prepare phase2 pot12_beacon.ptau pot12_final.ptau" >>= shouldBe ExitSuccess
  --     system "snarkjs powersoftau verify pot12_final.ptau" >>= shouldBe ExitSuccess
  --   it "Generating zkey..." $ do
  --     system ("snarkjs groth16 setup " <> name <> ".r1cs pot12_final.ptau " <> name <> ".zkey") >>= shouldBe ExitSuccess
  -- describe ("Setting up and generating Groth16 proof for " <> name <> "...") $ do
  --   it "Generating Groth16 proof..." $ do
  --     system ("snarkjs groth16 prove " <> name <> ".zkey " <> name <> ".wtns proof.json public.json") >>= shouldBe ExitSuccess
  --   it "Exporting verification key..." $ do
  --     system ("snarkjs zkey export verificationkey <> " <> name <> ".zkey " <> name <> "_verification_key.jsonl") >>= shouldBe ExitSuccess
  --   it "Verifying Groth16 proof..." $ do
  --     system ("snarkjs groth16 verify " <> name <> "_verification_key.jsonl public.json proof.json") >>= shouldBe ExitSuccess

tests :: SpecWith ()
tests = do
  describe "Testing Quad" $ do
    it "should pass: a,b,c,d = 3,5,-22,2" $ do
      runAll bn128 quad [3, 5, -22] [2] []

-- testWith "sudoku" sudoku testProblem testSolution

testQuad :: SpecWith ()
testQuad = describe "Quad properties" $ do
  it "should preserve invariants after applying randomized adjustments" $ do
    forAll (suchThat arbitrary (\(a, b, c, x) ->  (a * x * x + b * x + c) == 0)) $ \(a, b, c, x) -> do
      genCircuitBin ("quad.r1cs") bn128 quad >>= flip shouldSatisfy isRight
      genWtns ("quad.wtns") bn128 quad [a,b,c] [x] >>= flip shouldSatisfy isRight
      -- system ("snarkjs groth16 verify  quad_verification_key.jsonl public.json proof.json") >>= shouldBe ExitSuccess
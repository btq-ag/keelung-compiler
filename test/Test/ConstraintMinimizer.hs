{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <&>" #-}
module Test.ConstraintMinimizer (tests, run) where

-- import Data.Foldable (toList)
-- import Hash.Poseidon qualified as Poseidon

import AggregateSignature.Util qualified as AggSig
import Data.Foldable
import Hash.Poseidon qualified as Poseidon
import Keelung hiding (compileO0, run)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.Compile qualified as Compiler
import Keelung.Compiler.Constraint
import Keelung.Compiler.Error (Error)
import Keelung.Compiler.Optimize qualified as Optimizer
import Keelung.Compiler.Optimize.ConstantPropagation qualified as ConstantPropagation
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Keelung.Compiler.Relocated qualified as Relocated
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Constraint.R1CS qualified as Compiler
import Keelung.Interpreter.R1CS qualified as R1CS
import Test.HUnit (assertFailure)
import Test.Hspec

-- | elaborate => rewrite => type erase => constant propagation => compile
compileO0 :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (ConstraintSystem n)
compileO0 program = Compiler.erase program >>= return . Compiler.run True . ConstantPropagation.run

runTest :: Encode t => Int -> Int -> Comp t -> IO (ConstraintSystem (N GF181))
runTest expectedBeforeSize expectedAfterSize program = do
  cs <- case Compiler.asGF181N $ compileO0 program of
    Left err -> assertFailure $ show err
    Right result -> return result

  let cs' = Optimizer.optimize1' cs

  -- let r1cs = Compiler.asGF181N $  Compiler.toR1CS <$> Compiler.compileO2 program
  -- print cs
  -- print cs'

  -- var counters should remain the same
  csCounters cs `shouldBe` csCounters cs'

  -- compare the number of constraints
  let actualBeforeSize = Relocated.numberOfConstraints (relocateConstraintSystem cs)
  actualBeforeSize `shouldBe` expectedBeforeSize
  let actualAfterSize = Relocated.numberOfConstraints (relocateConstraintSystem cs')
  actualAfterSize `shouldBe` expectedAfterSize

  return cs'

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "Constraint minimization" $ do
    it "Poseidon" $ do
      _cs <- runTest 1537 855 $ do
        xs <- inputs 1
        Poseidon.hash (toList xs)
      return ()

    it "Union Find 1" $ do
      cs <- runTest 3 1 $ do
        x <- inputField
        y <- reuse x
        z <- reuse x
        return (x + y + z)

      -- FO0 = 3FI0
      UnionFind.relationBetween (RefFO 0) (RefFI 0) (csVarEqF cs) `shouldBe` Just (3, 0)
      -- F0 (y) = FI0
      UnionFind.relationBetween (RefF 0) (RefFI 0) (csVarEqF cs) `shouldBe` Just (1, 0)
      -- F1 (z) = F0 (y)
      UnionFind.relationBetween (RefF 1) (RefF 0) (csVarEqF cs) `shouldBe` Just (1, 0)

    it "Union Find 2" $ do
      cs <- runTest 3 1 $ do
        x <- inputField
        y <- reuse x
        z <- reuse (x + y)
        return (x + y + z)

      -- FO0 = 4FI0
      UnionFind.relationBetween (RefFO 0) (RefFI 0) (csVarEqF cs) `shouldBe` Just (4, 0)
      -- F0 (y) = FI0
      UnionFind.relationBetween (RefF 0) (RefFI 0) (csVarEqF cs) `shouldBe` Just (1, 0)
      -- F1 (z) = 2F0 (y)
      UnionFind.relationBetween (RefF 1) (RefF 0) (csVarEqF cs) `shouldBe` Just (2, 0)

    it "Union Find 3" $ do
      cs <- runTest 2 1 $ do
        x <- inputField
        y <- reuse (x + 1)
        return (x + y)

      -- FO0 = 2FI0 + 1
      UnionFind.relationBetween (RefFO 0) (RefFI 0) (csVarEqF cs) `shouldBe` Just (2, 1)

    it "Union Find 4" $ do
      cs <- runTest 1 1 $ do
        let x = 4
        y <- reuse x
        return (x + y :: Field)
      -- print cs
      -- print $ relocateConstraintSystem cs
      -- FO0 = 8
      snd (UnionFind.lookup (RefFO 0) (csVarEqF cs)) `shouldBe` (Nothing, 8)

    it "Union Find 5" $ do
      _cs <- runTest 2 2 $ do
        x <- inputField
        y <- reuse x
        return (x * y :: Field)
      return ()
      -- print cs
      -- print $ relocateConstraintSystem cs

  -- describe "Aggregate Signature" $ do
  --   it "dim:1 sig:10" runAllKeelungAggSig

-- it "Range check on Field (< 12289)" $ do
--   cs <- runTest 6 5 $ do
--     value <- inputField
--     let dimension = 2
--     bits <- inputs dimension

--     let summation = foldl (\acc k ->
--                           let bit = access bits k
--                               bitValue = fromInteger (2 ^ k :: Integer)
--                               prod = bit * bitValue
--                           in  (acc + prod))  0 [0 .. dimension - 1]
--     assert (value `eq` summation)

--     let bit13 = access bits (dimension - 1)
--     let bit12 = access bits (dimension - 2)
--     let bit11to0 = foldl (\acc k ->
--                             let bit = access bits k
--                             in  acc + bit) 0 [0 .. dimension - 3]

--     let smallerThan12289 = bit13 * bit12 * bit11to0
--     assert (smallerThan12289 `eq` 0)

--   print cs
--   print $ relocateConstraintSystem cs

--   return ()


interpretCS :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) [n]
interpretCS prog rawInputs = do
  r1cs' <- Compiler.toR1CS . relocateConstraintSystem <$> Compiler.compileO1' prog
  let inps = Inputs.deserialize (Compiler.r1csCounters r1cs') rawInputs
  case R1CS.run r1cs' inps of
    Left err -> Left (Compiler.InterpretError err)
    Right outputs -> Right (Inputs.removeBinRepsFromOutputs (Compiler.r1csCounters r1cs') outputs)

testInterpret :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> IO ()
testInterpret program rawInputs rawOutputs = do
  interpretCS program rawInputs
    `shouldBe` Right rawOutputs

runAllKeelungAggSig :: IO ()
runAllKeelungAggSig =
  testInterpret
    checkSize
    [0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0 :: GF181]
    []

checkSize :: Comp ()
checkSize = do
  let signatures = [11324, 5247]
  sigBitStrings <- inputs2 2 14
  forM_ [0 .. 1] $ \i -> do
    let signature = signatures !! i
    let coeff = signature
    -- within the range of [0, 16384)
    let value =
          foldl
            ( \acc k ->
                let bit = access2 sigBitStrings (i, k)
                    bitValue = fromIntegral (2 ^ k :: Integer)
                    prod = BtoF bit * bitValue
                 in (acc + prod)
            )
            0
            [0 .. 13]
    assert (coeff `eq` value)

    let bit13 = access2 sigBitStrings (i, 13)
    let bit12 = access2 sigBitStrings (i, 12)
    let bit11to0 =
          foldl
            ( \acc k ->
                let bit = access2 sigBitStrings (i, k)
                 in acc + BtoF bit
            )
            0
            [0 .. 11]

    let smallerThan12289 = BtoF bit13 * BtoF bit12 * bit11to0
    assert (smallerThan12289 `eq` 0)

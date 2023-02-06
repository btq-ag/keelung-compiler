{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <&>" #-}
module Test.ConstraintMinimizer (tests, run) where

import Data.Map.Strict qualified as Map
import Keelung hiding (compileO0, run)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.Compile qualified as Compiler
import Keelung.Compiler.Constraint
import Keelung.Compiler.Error (Error)
import Keelung.Compiler.Optimize qualified as Optimizer
import Keelung.Compiler.Optimize.ConstantPropagation qualified as ConstantPropagation
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Keelung.Compiler.Relocated qualified as Relocated
import Test.HUnit (assertFailure)
import Test.Hspec
import qualified Hash.Poseidon as Poseidon
import Data.Foldable (toList)

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
    -- it "Poseidon" $ do
    --   cs <- runTest 1537 855 $ do
    --     xs <- inputs 1
    --     Poseidon.hash (toList xs)

    --   Map.toList (UnionFind.toMap (csVarEqF cs))
    --     `shouldContain` []

    -- it "Union Find 1" $ do
    --   cs <- runTest 3 1 $ do
    --     x <- inputField
    --     y <- reuse x
    --     z <- reuse x
    --     return (x + y + z)

    --   Map.toList (UnionFind.toMap (csVarEqF cs))
    --     `shouldContain` [(RefF 0, (Just (1, RefFI 0), 0))]
    --   Map.toList (UnionFind.toMap (csVarEqF cs))
    --     `shouldContain` [(RefF 1, (Just (1, RefFI 0), 0))]

    it "Union Find 2" $ do
      cs <- runTest 3 1 $ do
        x <- inputField
        y <- reuse x
        z <- reuse (x + y)
        return (x + y + z)

      print cs

      -- FO0 = 4FI0 
      UnionFind.relationBetween (RefFO 0) (RefFI 0) (csVarEqF cs) `shouldBe` Just (4, 0)

      -- Map.toList (UnionFind.toMap (csVarEqF cs))
      --   `shouldContain` [(RefFO 0, (Just (4, RefFI 0), 0))]

    -- it "Union Find 3" $ do
    --   cs <- runTest 2 1 $ do
    --     x <- inputField
    --     y <- reuse (x + 1)
    --     return (x + y)

    --   Map.toList (UnionFind.toMap (csVarEqF cs))
    --     `shouldContain` [(RefFO 0, (Just (2, RefFI 0), 1))]

    --   Map.toList (UnionFind.toMap (csVarEqF cs))
    --     `shouldContain` [(RefF 0, (Just (1, RefFI 0), 1))]

    -- it "Union Find 4" $ do
    --   cs <- runTest 2 2 $ do
    --     let x = 4
    --     y <- reuse x
    --     return (x + y :: Field)

    --   print cs 

    --   Map.toList (UnionFind.toMap (csVarEqF cs))
    --     `shouldContain` [(RefFO 0, (4, RefFI 0, 0))]

    -- -- within the range of [0, 12289)
    -- it "Manual range check (< 12289)" $ do
    --   void $ runTest 49 49 $ do 
    --     value <- input
    --     bits <- inputs 14

    --     let summation = foldl (\acc k ->
    --                           let bit = access bits k
    --                               bitValue = fromIntegral (2 ^ k :: Integer)
    --                               prod = BtoF bit * bitValue
    --                           in  (acc + prod))  0 [0 .. 13]
    --     assert (value `eq` summation)

    --     let bit13 = access bits 13
    --     let bit12 = access bits 12
    --     let bit11to0 = foldl (\acc k ->
    --                             let bit = access bits k
    --                             in  acc + BtoF bit) 0 [0 .. 11]

    --     let smallerThan12289 = BtoF bit13 * BtoF bit12 * bit11to0
    --     assert (smallerThan12289 `eq` 0)

    -- it "Fake range check on Field" $ do
    --   void $ runTest 7 7 $ do 
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

-- it "Basic.summation2" $ do
--   runTest 1 Basic.summation2
-- it "Basic.assertArraysEqual2" $ do
--   runTest 0 Basic.assertArraysEqual2
-- it "Basic.assert1" $ do
--   runTest 1 Basic.assert1
-- it "Basic.returnArray2" $ do
--   runTest 2 Basic.returnArray2
-- it "Poseidon Hash 1" $ do
--   _cs <- runTest 1665 $ do
--         x <- input
--         Poseidon.hash [x]
--   return ()
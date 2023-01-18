{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <&>" #-}
module Test.ConstraintMinimizer (tests, run) where

-- import qualified Basic

import qualified Data.Map.Strict as Map
import Keelung hiding (run)
import qualified Keelung.Compiler as Compiler
import qualified Keelung.Compiler.Compile as Compiler
import Keelung.Compiler.Constraint
import Keelung.Compiler.Error (Error)
import qualified Keelung.Compiler.Optimize as Optimizer
import qualified Keelung.Compiler.Optimize.ConstantPropagation as ConstantPropagation
import qualified Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind as UnionFind
import qualified Keelung.Compiler.Relocated as Relocated
import Test.HUnit
import Test.Hspec

-- | elaborate => rewrite => type erase => constant propagation => compile
compileOnly :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (ConstraintSystem n)
compileOnly program = Compiler.erase program >>= return . Compiler.run . ConstantPropagation.run

runTest :: Encode t => Int -> Comp t -> IO (ConstraintSystem (N GF181))
runTest expectedSize program = do
  cs <- case Compiler.asGF181N $ compileOnly program of
    Left err -> assertFailure $ show err
    Right result -> return result

  let cs' = Optimizer.optimize1' cs

  -- let r1cs = Compiler.asGF181N $  Compiler.toR1CS <$> Compiler.compileO2 program
  -- print cs
  -- print cs'

  -- var counters should remain the same
  csCounters cs `shouldBe` csCounters cs'

  -- compare the number of constraints
  let actualSize = Relocated.numberOfConstraints (relocateConstraintSystem cs')
  actualSize `shouldBe` expectedSize

  return cs'

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "Constraint minimization" $ do
    it "Union Find 1" $ do
      cs <- runTest 3 $ do
        x <- inputField
        y <- reuse x
        z <- reuse x
        return (x + y + z)

      Map.toList (UnionFind.toMap (csVarEqF cs))
        `shouldContain` [(RefFO 0, (3, RefFI 0))]

    it "Union Find 2" $ do
      cs <- runTest 3 $ do
        x <- inputField
        y <- reuse x
        z <- reuse (x + y)
        return (x + y + z)

      Map.toList (UnionFind.toMap (csVarEqF cs))
        `shouldContain` [(RefFO 0, (4, RefFI 0))]

-- it "Basic.summation" $ do
--   runTest 1 Basic.summation
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
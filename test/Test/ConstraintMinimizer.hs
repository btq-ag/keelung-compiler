{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <&>" #-}
module Test.ConstraintMinimizer (tests, run) where

-- import qualified Basic

-- import Data.Foldable (Foldable (toList))
import Data.Map.Strict qualified as Map
-- import Hash.Poseidon qualified as Poseidon
import Keelung hiding (run)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.Compile qualified as Compiler
import Keelung.Compiler.Constraint
import Keelung.Compiler.Error (Error)
import Keelung.Compiler.Optimize qualified as Optimizer
import Keelung.Compiler.Optimize.ConstantPropagation qualified as ConstantPropagation
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Keelung.Compiler.Relocated qualified as Relocated
import Test.HUnit
import Test.Hspec

-- | elaborate => rewrite => type erase => constant propagation => compile
compileOnly :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (ConstraintSystem n)
compileOnly program = Compiler.erase program >>= return . Compiler.run . ConstantPropagation.run

runTest :: Encode t => Int -> Int -> Comp t -> IO (ConstraintSystem (N GF181))
runTest expectedBeforeSize expectedAfterSize program = do
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
    --   cs <- runTest 1536 1536 $ do
    --     xs <- inputs 1
    --     Poseidon.hash (toList xs)

    --   Map.toList (UnionFind.toMap (csVarEqF cs))
    --     `shouldContain` []

    it "Union Find 1" $ do
      cs <- runTest 1 1 $ do
        x <- inputField
        y <- reuse x
        z <- reuse x
        return (x + y + z)

      Map.toList (UnionFind.toMap (csVarEqF cs))
        `shouldContain` [(RefFO 0, (3, RefFI 0))]

    it "Union Find 2" $ do
      cs <- runTest 2 1 $ do
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
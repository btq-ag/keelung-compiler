{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <&>" #-}
module Test.ConstraintMinimizer (tests) where

-- import qualified Basic
import Keelung
import qualified Keelung.Compiler as Compiler
import qualified Keelung.Compiler.Compile as Compiler
import Keelung.Compiler.Constraint
import Keelung.Compiler.Error (Error)
import qualified Keelung.Compiler.Optimize as Optimizer
import qualified Keelung.Compiler.Optimize.ConstantPropagation as ConstantPropagation
import Test.Hspec

-- | elaborate => rewrite => type erase => constant propagation => compile
compileOnly :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (ConstraintSystem n)
compileOnly program = Compiler.erase program >>= return . Compiler.run . ConstantPropagation.run

runTest :: Encode t => Int -> Comp t -> IO ()
runTest expectedSize program = do
  let cs = Compiler.asGF181N $ compileOnly program
  let cs' = Optimizer.optimize1' <$> cs

--   let r1cs = Compiler.asGF181N $  Compiler.toR1CS <$> Compiler.compileO2 program
  -- print cs'

  -- var counters should remain the same
  csCounters <$> cs `shouldBe` csCounters <$> cs'

  sizeOfConstraintSystem <$> cs' `shouldBe` Right expectedSize

tests :: SpecWith ()
tests = do
  describe "Constraint minimization" $ do
    it "VarBindF" $ do
      runTest 2 $ do 
        reuse (3 :: Field) 
        


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
    --     runTest 1665 $ do 
    --         x <- input
    --         Poseidon.hash [x]
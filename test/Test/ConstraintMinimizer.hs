{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <&>" #-}
module Test.ConstraintMinimizer (tests) where

import Keelung
import qualified Keelung.Compiler as Compiler
import qualified Keelung.Compiler.Compile as Compiler
import Keelung.Compiler.Constraint
import Keelung.Compiler.Error (Error)
import qualified Keelung.Compiler.Optimize as Optimizer
import qualified Keelung.Compiler.Optimize.ConstantPropagation as ConstantPropagation
import Test.Hspec
-- import Debug.Trace

-- | elaborate => rewrite => type erase => constant propagation => compile
compileOnly :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (ConstraintSystem n)
compileOnly program = Compiler.erase program >>= return . Compiler.run . ConstantPropagation.run

runTest :: Encode t => Comp t -> IO ()
runTest program = do
  let cs = Compiler.asGF181N $ compileOnly program
  let cs' = Optimizer.optimize1' <$> cs

--   traceShowM cs
--   traceShowM cs'

  -- var counters should remain the same
  csCounters <$> cs `shouldBe` csCounters <$> cs'

tests :: SpecWith ()
tests = do
  describe "Constraint minimization" $ do
    it "1" $ do
        runTest $ do
            x <- inputField 
            assert $ x `eq` 4
            y <- inputField
            return $ x + y
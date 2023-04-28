{-# LANGUAGE DataKinds #-}
module Test.Optimization.UInt (tests, run, debug) where

import Keelung hiding (compileO0, run)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.Compile qualified as Compiler
import Keelung.Compiler.ConstraintSystem (ConstraintSystem (..), relocateConstraintSystem)
import Keelung.Compiler.Error (Error)
import Keelung.Compiler.Optimize qualified as Optimizer
import Keelung.Compiler.Optimize.ConstantPropagation qualified as ConstantPropagation
import Keelung.Compiler.Relocated qualified as Relocated
import Test.HUnit (assertFailure)
import Test.Hspec

tests :: SpecWith ()
tests = do
  describe "UInt" $ do
      it "compute LTE" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ x `lte` y
        cs `shouldHaveSize` 20
        cs' `shouldHaveSize` 19

      it "compute LT" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ x `lt` y
        cs `shouldHaveSize` 19
        cs' `shouldHaveSize` 18

      it "compute GTE" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ x `gte` y
        cs `shouldHaveSize` 20
        cs' `shouldHaveSize` 19

      it "compute GT" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ x `gt` y
        cs `shouldHaveSize` 19
        cs' `shouldHaveSize` 18

      it "compute LTE" $ do
        (cs, cs') <- execute $ do
          return $ 0 `lte` (0  :: UInt 4)
        cs `shouldHaveSize` 18
        cs' `shouldHaveSize` 6

--------------------------------------------------------------------------------


-- | elaborate => rewrite => type erase => constant propagation => compile
compileO0 :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (ConstraintSystem n)
compileO0 program = Compiler.erase program >>= Compiler.run True . ConstantPropagation.run

-- | Returns the original and optimized constraint system
execute :: Encode t => Comp t -> IO (ConstraintSystem (N GF181), ConstraintSystem (N GF181))
execute program = do
  cs <- case Compiler.asGF181N $ compileO0 program of
    Left err -> assertFailure $ show err
    Right result -> return result

  case Optimizer.optimizeNew cs of
    Left err -> assertFailure $ show err
    Right cs' -> do 
        -- var counters should remain the same
        csCounters cs `shouldBe` csCounters cs'
        return (cs, cs')

shouldHaveSize :: ConstraintSystem (N GF181) -> Int -> IO ()
shouldHaveSize cs expectedBeforeSize = do
  -- compare the number of constraints
  let actualBeforeSize = Relocated.numberOfConstraints (relocateConstraintSystem cs)
  actualBeforeSize `shouldBe` expectedBeforeSize

run :: IO ()
run = hspec tests

debug :: ConstraintSystem (N GF181) -> IO ()
debug cs = do
  print cs
  print (relocateConstraintSystem cs)

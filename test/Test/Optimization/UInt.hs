{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
module Test.Optimization.UInt (tests, run, debug) where

import Keelung hiding (compileO0)
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
    describe "Constants" $ do
      it "`return 0`" $ do
        (cs, cs') <- execute $ do
          return (0  :: UInt 4)
        cs `shouldHaveSize` 6
        cs' `shouldHaveSize` 6

      -- it "`return 0[3]`" $ do
      --   (cs, cs') <- execute $ do
      --     let a = 0  :: UInt 4
      --     return $ a !!! 3
      --   debug cs'
      --   cs `shouldHaveSize` 2
      --   cs' `shouldHaveSize` 2

    describe "Comparison" $ do
      it "compute LTE (variable / variable)" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ x `lte` y
        cs `shouldHaveSize` 19
        cs' `shouldHaveSize` 18

      it "compute LTE 1 (variable / constant)" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          return $ (0  :: UInt 4) `lte` x
        cs `shouldHaveSize` 7
        cs' `shouldHaveSize` 7

      it "compute LTE 2 (variable / constant)" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          return $ (1  :: UInt 4) `lte` x
        cs `shouldHaveSize` 10
        cs' `shouldHaveSize` 9

      it "compute LTE 1 (constant / variable)" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          return $ x `lte` (0  :: UInt 4)
        cs `shouldHaveSize` 11
        cs' `shouldHaveSize` 9

      it "compute LTE 2 (constant / variable)" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          return $ x `lte` (1  :: UInt 4)
        cs `shouldHaveSize` 10
        cs' `shouldHaveSize` 8

      it "compute LTE (constant / constant)" $ do
        (cs, cs') <- execute $ do
          return $ 0 `lte` (0  :: UInt 4)
        cs `shouldHaveSize` 2
        cs' `shouldHaveSize` 2

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
        cs `shouldHaveSize` 19
        cs' `shouldHaveSize` 18

      it "compute GT" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ x `gt` y
        cs `shouldHaveSize` 19
        cs' `shouldHaveSize` 18

--------------------------------------------------------------------------------


-- | elaborate => rewrite => to internal syntax => constant propagation => compile
compileO0 :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (ConstraintSystem n)
compileO0 program = Compiler.convertToInternal program >>= Compiler.run True . ConstantPropagation.run

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

{-# LANGUAGE ScopedTypeVariables #-}

module Test.Optimization.Util (debug, executeGF181, executePrime, shouldHaveSize) where

import Data.Field.Galois (Prime)
import Data.Proxy (Proxy)
import Keelung hiding (compileO0)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.ConstraintSystem qualified as ConstraintSystem
import Keelung.Compiler.Linker qualified as Linker
import Keelung.Compiler.Optimize qualified as Optimizer
import Keelung.Data.FieldInfo
import Test.HUnit (assertFailure)
import Test.Hspec
import Test.Interpreter.Util (gf181Info)

--------------------------------------------------------------------------------

-- | Returns the original and optimized constraint system
executeGF181 :: Encode t => Comp t -> IO (ConstraintModule (N GF181), ConstraintModule (N GF181))
executeGF181 program = do
  cm <- case Compiler.compileO0 gf181Info program of
    Left err -> assertFailure $ show err
    Right result -> return result

  case Optimizer.run cm of
    Left err -> assertFailure $ show err
    Right cm' -> do
      -- var counters should remain the same
      cmCounters cm `shouldBe` cmCounters cm'
      return (cm, cm')

-- | Returns the original and optimized constraint system
executePrime :: (Encode t, GaloisField n, Integral n) => Integer -> Comp t -> IO (ConstraintModule n, ConstraintModule n)
executePrime n program = caseFieldType (Prime n) handlePrime undefined
  where
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      cm <- case Compiler.compileO0 fieldInfo program of
        Left err -> assertFailure $ show err
        Right result -> return result
      case Optimizer.run cm of
        Left err -> assertFailure $ show err
        Right cm' -> do
          -- var counters should remain the same
          cmCounters cm `shouldBe` cmCounters cm'
          return (cm, cm')

shouldHaveSize :: ConstraintModule (N GF181) -> Int -> IO ()
shouldHaveSize cm expectedBeforeSize = do
  -- compare the number of constraints
  let actualBeforeSize = ConstraintSystem.numberOfConstraints (Linker.linkConstraintModule cm)
  actualBeforeSize `shouldBe` expectedBeforeSize

debug :: ConstraintModule (N GF181) -> IO ()
debug cm = do
  print cm
  print (Linker.linkConstraintModule cm)
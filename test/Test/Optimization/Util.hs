{-# LANGUAGE ScopedTypeVariables #-}

module Test.Optimization.Util (debug, executeGF181, executeGF181', executePrime, executeBinary, shouldHaveSize) where

import Control.Arrow (left)
import Data.Field.Galois (Binary, Prime)
import Data.Proxy (Proxy)
import Keelung hiding (compileWithOpts)
import Keelung.Compiler (Error, compileWithOpts)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.ConstraintSystem qualified as ConstraintSystem
import Keelung.Compiler.Linker qualified as Linker
import Keelung.Compiler.Optimize qualified as Optimizer
import Keelung.Compiler.Options
import Keelung.Data.FieldInfo
import Test.Compilation.Util (gf181Info)
import Test.HUnit (assertFailure)
import Test.Hspec

--------------------------------------------------------------------------------

-- | Returns the original and optimized constraint system
executeGF181WithOpts :: (Encode t) => Options -> Comp t -> IO (ConstraintModule (N GF181), ConstraintModule (N GF181))
executeGF181WithOpts options program = do
  let optionsO0 = options {optOptimize = False}
  -- without optimization
  cm <- case compileWithOpts optionsO0 program of
    Left err -> assertFailure $ show err
    Right result -> return result

  -- with optimization
  case optimize cm of
    Left err -> assertFailure $ show err
    Right cm' -> do
      -- var counters should remain the same
      cmCounters cm `shouldBe` cmCounters cm'
      return (cm, cm')

executeGF181 :: (Encode t) => Comp t -> IO (ConstraintModule (N GF181), ConstraintModule (N GF181))
executeGF181 = executeGF181WithOpts (defaultOptions {optFieldInfo = gf181Info})

executeGF181' :: (Encode t) => Comp t -> IO (ConstraintModule (N GF181), ConstraintModule (N GF181))
executeGF181' = executeGF181WithOpts (defaultOptions {optFieldInfo = gf181Info, optUseNewLinker = True})

-- | Returns the original and optimized constraint system
executePrime :: (Encode t, GaloisField n, Integral n) => Integer -> Comp t -> IO (ConstraintModule n, ConstraintModule n)
executePrime n program = caseFieldType (Prime n) handlePrime undefined
  where
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = do
      cm <- case compileWithOpts (defaultOptions {optFieldInfo = fieldInfo, optOptimize = False}) program of
        Left err -> assertFailure $ show err
        Right result -> return result
      case optimize cm of
        Left err -> assertFailure $ show err
        Right cm' -> do
          -- var counters should remain the same
          cmCounters cm `shouldBe` cmCounters cm'
          return (cm, cm')

-- | Returns the original and optimized constraint system
executeBinary :: (Encode t, GaloisField n, Integral n) => Integer -> Comp t -> IO (ConstraintModule n, ConstraintModule n)
executeBinary n program = caseFieldType (Binary n) undefined handleBinary
  where
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = do
      cm <- case compileWithOpts (defaultOptions {optFieldInfo = fieldInfo, optOptimize = False}) program of
        Left err -> assertFailure $ show err
        Right result -> return result
      case optimize cm of
        Left err -> assertFailure $ show err
        Right cm' -> do
          -- var counters should remain the same
          cmCounters cm `shouldBe` cmCounters cm'
          return (cm, cm')

shouldHaveSize :: ConstraintModule (N GF181) -> Int -> IO ()
shouldHaveSize cm expecteds = do
  -- compare the number of constraints
  let actual = ConstraintSystem.numberOfConstraints (Linker.linkConstraintModule cm)
  actual `shouldBe` expecteds

optimize :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Error n) (ConstraintModule n)
optimize = left Compiler.CompilerError . Optimizer.run

debug :: ConstraintModule (N GF181) -> IO ()
debug cm = do
  print cm
  print (Linker.linkConstraintModule cm)
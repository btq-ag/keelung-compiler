{-# LANGUAGE ScopedTypeVariables #-}

module Test.Optimization.Util (debug, executeGF181, executePrime, shouldHaveSize) where

import Control.Arrow (left)
import Control.Monad ((>=>))
import Data.Field.Galois (Prime)
import Data.Proxy (Proxy)
import Keelung hiding (compile)
import Keelung.Compiler (Error)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.ConstraintSystem qualified as ConstraintSystem
import Keelung.Compiler.Linker qualified as Linker
import Keelung.Compiler.Optimize qualified as Optimizer
import Keelung.Data.FieldInfo
import Test.Compilation.Util (gf181Info)
import Test.HUnit (assertFailure)
import Test.Hspec

--------------------------------------------------------------------------------

-- | Returns the original and optimized constraint system
executeGF181 :: Encode t => Comp t -> IO (ConstraintModule (N GF181), ConstraintModule (N GF181))
executeGF181 program = do
  cm <- case compile gf181Info program of
    Left err -> assertFailure $ show err
    Right result -> return result

  case optimize cm of
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
      cm <- case compile (fieldInfo :: FieldInfo) program of
        Left err -> assertFailure $ show err
        Right result -> return result
      case optimize cm of
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

compile :: (Encode t, GaloisField n, Integral n) => FieldInfo -> Comp t -> Either (Error n) (ConstraintModule n)
compile fieldInfo = Compiler.elaborateAndEncode >=> Compiler.compileO0Elab fieldInfo

optimize :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Error n) (ConstraintModule n)
optimize = left Compiler.CompilerError . Optimizer.run

debug :: ConstraintModule (N GF181) -> IO ()
debug cm = do
  print cm
  print (Linker.linkConstraintModule cm)
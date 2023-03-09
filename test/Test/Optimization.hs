{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Test.Optimization (tests, run) where

import Data.Foldable
import Hash.Poseidon qualified as Poseidon
import Keelung hiding (compileO0, run)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.Compile qualified as Compiler
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintSystem (ConstraintSystem (..), relocateConstraintSystem)
import Keelung.Compiler.Error (Error)
import Keelung.Compiler.Optimize qualified as Optimizer
import Keelung.Compiler.Optimize.ConstantPropagation qualified as ConstantPropagation
import Keelung.Compiler.Optimize.MinimizeConstraints.FieldRelations qualified as FieldRelations
import Keelung.Compiler.Relocated qualified as Relocated
import Test.HUnit (assertFailure)
import Test.Hspec

-- | elaborate => rewrite => type erase => constant propagation => compile
compileO0 :: (GaloisField n, Integral n, Encode t) => Comp t -> Either (Error n) (ConstraintSystem n)
compileO0 program = Compiler.erase program >>= return . Compiler.run True . ConstantPropagation.run

runTest :: Encode t => Int -> Int -> Comp t -> IO (ConstraintSystem (N GF181))
runTest expectedBeforeSize expectedAfterSize program = do
  cs <- case Compiler.asGF181N $ compileO0 program of
    Left err -> assertFailure $ show err
    Right result -> return result

  let cs' = Optimizer.optimize1' cs

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
    it "Poseidon" $ do
      _cs <- runTest 1537 694 $ do
        xs <- inputList Public 1
        Poseidon.hash (toList xs)

      -- print _cs
      -- print (relocateConstraintSystem _cs)

      return ()

    it "Field 1" $ do
      cs <- runTest 3 1 $ do
        x <- inputField Public
        y <- reuse x
        z <- reuse x
        return (x + y + z)

      -- FO0 = 3FI0
      FieldRelations.relationBetween (RefFO 0) (RefFI 0) (csFieldRelations cs) `shouldBe` Just (3, 0)
      -- F0 (y) = FI0
      FieldRelations.relationBetween (RefF 0) (RefFI 0) (csFieldRelations cs) `shouldBe` Just (1, 0)
      -- F1 (z) = F0 (y)
      FieldRelations.relationBetween (RefF 1) (RefF 0) (csFieldRelations cs) `shouldBe` Just (1, 0)

    it "Field 2" $ do
      cs <- runTest 3 1 $ do
        x <- inputField Public
        y <- reuse x
        z <- reuse (x + y)
        return (x + y + z)

      -- FO0 = 4FI0
      FieldRelations.relationBetween (RefFO 0) (RefFI 0) (csFieldRelations cs) `shouldBe` Just (4, 0)
      -- F0 (y) = FI0
      FieldRelations.relationBetween (RefF 0) (RefFI 0) (csFieldRelations cs) `shouldBe` Just (1, 0)
      -- F1 (z) = 2F0 (y)
      FieldRelations.relationBetween (RefF 1) (RefF 0) (csFieldRelations cs) `shouldBe` Just (2, 0)

    it "Field 3" $ do
      cs <- runTest 2 1 $ do
        x <- inputField Public
        y <- reuse (x + 1)
        return (x + y)

      -- FO0 = 2FI0 + 1
      FieldRelations.relationBetween (RefFO 0) (RefFI 0) (csFieldRelations cs) `shouldBe` Just (2, 1)

    it "Field 4" $ do
      cs <- runTest 1 1 $ do
        let x = 4
        y <- reuse x
        return (x + y :: Field)
      FieldRelations.parentOf (csFieldRelations cs) (RefFO 0) `shouldBe` FieldRelations.Constant 8

    it "Field 5" $ do
      _cs <- runTest 2 1 $ do
        x <- inputField Public
        y <- reuse x
        return (x * y :: Field)
      return ()

    it "Boolean 1" $ do
      _cs <- runTest 4 3 $ do
        x <- inputBool Public
        y <- reuse x
        return (x .|. y)
      return ()

    it "Boolean 2" $ do
      _cs <- runTest 3 3 $ do
        x <- inputBool Public
        reuse x
      return ()

    -- it "UInt / Value" $ do
    --   _cs <- runTest 6 6 $ do
    --     let x = 3 :: UInt 4
    --     return x
    --   print _cs
    --   print $ relocateConstraintSystem _cs
    --   return ()

    it "UInt / Variable" $ do
      _cs <- runTest 11 11 $ do
        x <- inputUInt Public :: Comp (UInt 4)
        reuse x
      return ()

    -- it "UInt add 1" $ do
    --   _cs <- runTest 40 40 $ do
    --     x <- inputUInt @4 Public
    --     y <- inputUInt @4 Public
    --     z <- inputUInt @4 Public
    --     w <- reuse $ x + y
    --     return $ x + y + z + w
    --   -- print _cs
    --   -- print $ relocateConstraintSystem _cs
    --   return ()

    -- it "UInt rotate 1" $ do
    --   _cs <- runTest 23 23 $ do
    --     x <- inputUInt @4 Public
    --     return [rotate x 0, rotate x 1]
    --   print _cs
    --   print $ relocateConstraintSystem _cs
    --   return ()
-- it "UInt 1" $ do
--   _cs <- runTest 15 11 $ do
--     x <- inputUInt Public :: Comp (UInt 4)
--     y <- reuse x
--     -- z <- reuse x
--     return (x + y)
--   print _cs
--   print $ relocateConstraintSystem _cs
--   return ()

-- it "Boolean 2" $ do
--   _cs <- runTest 15 15 $ do
--     x <- inputField Public
--     return (x `eq` 100 .|. x `eq` 200 .|. x `eq` 300)

--   print _cs
--   print $ relocateConstraintSystem _cs
--   return ()

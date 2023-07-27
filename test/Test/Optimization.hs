{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Test.Optimization (tests, run) where

import Data.Foldable
import Hash.Poseidon qualified as Poseidon
import Keelung hiding (compileO0)
import Keelung.Compiler.Relations.Field qualified as AllRelations
import Keelung.Data.Constraint
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Test.Hspec
import Test.Optimization.UInt qualified as Optimization.UInt
import Test.Optimization.Util

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "Constraint minimization" $ do
    Optimization.UInt.tests

    it "Poseidon" $ do
      (cm, cm') <- executeGF181 $ do
        xs <- inputList Public 1
        Poseidon.hash (toList xs)

      -- cm before `pow`: 1537
      cm `shouldHaveSize` 555
      -- cm' before `pow`: 694
      cm' `shouldHaveSize` 552

      return ()
      
    describe "Field" $ do
      it "Field 1" $ do
        (cm, cm') <- executeGF181 $ do
          x <- inputField Public
          y <- reuse x
          z <- reuse x
          return (x + y + z)

        cm `shouldHaveSize` 3
        cm' `shouldHaveSize` 1

        -- FO0 = 3FI0
        AllRelations.relationBetween (F $ RefFO 0) (F $ RefFI 0) (cmFieldRelations cm') `shouldBe` Just (3, 0)
        -- F0 (y) = FI0
        AllRelations.relationBetween (F $ RefFX 0) (F $ RefFI 0) (cmFieldRelations cm') `shouldBe` Just (1, 0)
        -- F1 (z) = F0 (y)
        AllRelations.relationBetween (F $ RefFX 1) (F $ RefFX 0) (cmFieldRelations cm') `shouldBe` Just (1, 0)

      it "Field 2" $ do
        (cm, cm') <- executeGF181 $ do
          x <- inputField Public
          y <- reuse x
          z <- reuse (x + y)
          return (x + y + z)

        cm `shouldHaveSize` 3
        cm' `shouldHaveSize` 1

        -- FO0 = 4FI0
        AllRelations.relationBetween (F $ RefFO 0) (F $ RefFI 0) (cmFieldRelations cm') `shouldBe` Just (4, 0)
        -- F0 (y) = FI0
        AllRelations.relationBetween (F $ RefFX 0) (F $ RefFI 0) (cmFieldRelations cm') `shouldBe` Just (1, 0)
        -- F1 (z) = 2F0 (y)
        AllRelations.relationBetween (F $ RefFX 1) (F $ RefFX 0) (cmFieldRelations cm') `shouldBe` Just (2, 0)

      it "Field 3" $ do
        (cm, cm') <- executeGF181 $ do
          x <- inputField Public
          y <- reuse (x + 1)
          return (x + y)

        cm `shouldHaveSize` 2
        cm' `shouldHaveSize` 1

        -- FO0 = 2FI0 + 1
        AllRelations.relationBetween (F $ RefFO 0) (F $ RefFI 0) (cmFieldRelations cm') `shouldBe` Just (2, 1)

      it "Field 4" $ do
        (cm, cm') <- executeGF181 $ do
          let x = 4
          y <- reuse x
          return (x + y :: Field)

        cm `shouldHaveSize` 1
        cm' `shouldHaveSize` 1
        AllRelations.lookup (F $ RefFO 0) (cmFieldRelations cm') `shouldBe` AllRelations.Value 8

      it "Field 5" $ do
        (cm, cm') <- executeGF181 $ do
          x <- inputField Public
          y <- reuse x
          return (x * y :: Field)
        cm `shouldHaveSize` 3
        cm' `shouldHaveSize` 1
        return ()

    describe "Boolean" $ do
      it "Boolean 1" $ do
        (cm, cm') <- executeGF181 $ do
          x <- inputBool Public
          y <- reuse x
          return (x .|. y)
        cm `shouldHaveSize` 5
        cm' `shouldHaveSize` 3

      it "Boolean 2" $ do
        (cm, cm') <- executeGF181 $ do
          x <- inputBool Public
          reuse x

        cm `shouldHaveSize` 3
        cm' `shouldHaveSize` 3

--     describe "Unsigned integers" $ do
--       it "literal" $ do
--         _cm <- runTest 10 10 $ do
--           let x = 3 :: UInt 4
--           return x
--         return ()

--       it "input + reuse" $ do
--         _cm <- runTest 11 11 $ do
--           x <- inputUInt Public :: Comp (UInt 4)
--           reuse x
--         return ()

--       it "rotate" $ do
--         _cm <- runTest 14 14 $ do
--           x <- inputUInt Public :: Comp (UInt 4)
--           return $ rotate x 1
--         -- print _cm
--         -- print $ linkConstraintModule _cm
--         return ()

--       it "add 1" $ do
--         _cm <- runTest 21 21 $ do
--           x <- inputUInt Public :: Comp (UInt 4)
--           y <- inputUInt Private :: Comp (UInt 4)
--           return (x + y)
--         return ()

-- -- it "UInt add 1" $ do
-- --   _cm <- runTest 40 40 $ do
-- --     x <- inputUInt @4 Public
-- --     y <- inputUInt @4 Public
-- --     z <- inputUInt @4 Public
-- --     w <- reuse $ x + y
-- --     return $ x + y + z + w
-- --   -- print _cm
-- --   -- print $ linkConstraintModule _cm
-- --   return ()

-- -- it "UInt 1" $ do
-- --   _cm <- runTest 15 11 $ do
-- --     x <- inputUInt Public :: Comp (UInt 4)
-- --     y <- reuse x
-- --     -- z <- reuse x
-- --     return (x + y)
-- --   print _cm
-- --   print $ linkConstraintModule _cm
-- --   return ()

-- -- it "Boolean 2" $ do
-- --   _cm <- runTest 15 15 $ do
-- --     x <- inputField Public
-- --     return (x `eq` 100 .|. x `eq` 200 .|. x `eq` 300)

-- --   print _cm
-- --   print $ linkConstraintModule _cm
-- --   return ()

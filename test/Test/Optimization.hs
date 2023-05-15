{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Test.Optimization (tests, run) where

import Data.Foldable
import Hash.Poseidon qualified as Poseidon
import Keelung hiding (compileO0)
import Keelung.Compiler.Relations.Field qualified as AllRelations
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintSystem (ConstraintSystem (..))
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
      (cs, cs') <- execute $ do
        xs <- inputList Public 1
        Poseidon.hash (toList xs)

      -- cs before `pow`: 1537
      cs `shouldHaveSize` 961
      -- cs' before `pow`: 552
      cs' `shouldHaveSize` 552

      return ()
    describe "Field" $ do
      it "Field 1" $ do
        (cs, cs') <- execute $ do
          x <- inputField Public
          y <- reuse x
          z <- reuse x
          return (x + y + z)

        cs `shouldHaveSize` 3
        cs' `shouldHaveSize` 1

        -- FO0 = 3FI0
        AllRelations.relationBetween (F $ RefFO 0) (F $ RefFI 0) (csFieldRelations cs') `shouldBe` Just (3, 0)
        -- F0 (y) = FI0
        AllRelations.relationBetween (F $ RefFX 0) (F $ RefFI 0) (csFieldRelations cs') `shouldBe` Just (1, 0)
        -- F1 (z) = F0 (y)
        AllRelations.relationBetween (F $ RefFX 1) (F $ RefFX 0) (csFieldRelations cs') `shouldBe` Just (1, 0)

      it "Field 2" $ do
        (cs, cs') <- execute $ do
          x <- inputField Public
          y <- reuse x
          z <- reuse (x + y)
          return (x + y + z)

        cs `shouldHaveSize` 3
        cs' `shouldHaveSize` 1

        -- FO0 = 4FI0
        AllRelations.relationBetween (F $ RefFO 0) (F $ RefFI 0) (csFieldRelations cs') `shouldBe` Just (4, 0)
        -- F0 (y) = FI0
        AllRelations.relationBetween (F $ RefFX 0) (F $ RefFI 0) (csFieldRelations cs') `shouldBe` Just (1, 0)
        -- F1 (z) = 2F0 (y)
        AllRelations.relationBetween (F $ RefFX 1) (F $ RefFX 0) (csFieldRelations cs') `shouldBe` Just (2, 0)

      it "Field 3" $ do
        (cs, cs') <- execute $ do
          x <- inputField Public
          y <- reuse (x + 1)
          return (x + y)

        cs `shouldHaveSize` 2
        cs' `shouldHaveSize` 1

        -- FO0 = 2FI0 + 1
        AllRelations.relationBetween (F $ RefFO 0) (F $ RefFI 0) (csFieldRelations cs') `shouldBe` Just (2, 1)

      it "Field 4" $ do
        (cs, cs') <- execute $ do
          let x = 4
          y <- reuse x
          return (x + y :: Field)

        cs `shouldHaveSize` 1
        cs' `shouldHaveSize` 1
        AllRelations.lookup (F $ RefFO 0) (csFieldRelations cs') `shouldBe` AllRelations.Value 8

      it "Field 5" $ do
        (cs, cs') <- execute $ do
          x <- inputField Public
          y <- reuse x
          return (x * y :: Field)
        debug cs
        cs `shouldHaveSize` 3
        cs' `shouldHaveSize` 1
        return ()

    describe "Boolean" $ do
      it "Boolean 1" $ do
        (cs, cs') <- execute $ do
          x <- inputBool Public
          y <- reuse x
          return (x .|. y)
        cs `shouldHaveSize` 5
        cs' `shouldHaveSize` 3

      it "Boolean 2" $ do
        (cs, cs') <- execute $ do
          x <- inputBool Public
          reuse x

        cs `shouldHaveSize` 3
        cs' `shouldHaveSize` 3

--     describe "Unsigned integers" $ do
--       it "literal" $ do
--         _cs <- runTest 10 10 $ do
--           let x = 3 :: UInt 4
--           return x
--         return ()

--       it "input + reuse" $ do
--         _cs <- runTest 11 11 $ do
--           x <- inputUInt Public :: Comp (UInt 4)
--           reuse x
--         return ()

--       it "rotate" $ do
--         _cs <- runTest 14 14 $ do
--           x <- inputUInt Public :: Comp (UInt 4)
--           return $ rotate x 1
--         -- print _cs
--         -- print $ relocateConstraintSystem _cs
--         return ()

--       it "add 1" $ do
--         _cs <- runTest 21 21 $ do
--           x <- inputUInt Public :: Comp (UInt 4)
--           y <- inputUInt Private :: Comp (UInt 4)
--           return (x + y)
--         return ()

-- -- it "UInt add 1" $ do
-- --   _cs <- runTest 40 40 $ do
-- --     x <- inputUInt @4 Public
-- --     y <- inputUInt @4 Public
-- --     z <- inputUInt @4 Public
-- --     w <- reuse $ x + y
-- --     return $ x + y + z + w
-- --   -- print _cs
-- --   -- print $ relocateConstraintSystem _cs
-- --   return ()

-- -- it "UInt 1" $ do
-- --   _cs <- runTest 15 11 $ do
-- --     x <- inputUInt Public :: Comp (UInt 4)
-- --     y <- reuse x
-- --     -- z <- reuse x
-- --     return (x + y)
-- --   print _cs
-- --   print $ relocateConstraintSystem _cs
-- --   return ()

-- -- it "Boolean 2" $ do
-- --   _cs <- runTest 15 15 $ do
-- --     x <- inputField Public
-- --     return (x `eq` 100 .|. x `eq` 200 .|. x `eq` 300)

-- --   print _cs
-- --   print $ relocateConstraintSystem _cs
-- --   return ()

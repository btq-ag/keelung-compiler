{-# LANGUAGE DataKinds #-}

-- {-# LANGUAGE TypeApplications #-}

module Test.Optimization.UInt.Misc (tests, run) where

import Keelung
-- import Keelung.Compiler.Linker
import Test.Hspec
import Test.Optimization.Util

-- --
run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Misc" $ do
  describe "Carry-less Multiplication" $ do
    it "2 2-bit variables" $ do
      -- constraint breakdown:
      -- I/O: 24 = 2 * 8 + 8
      -- ANDs: 36 = 8 * 9 / 2
      -- XORs: 7
      (_cs, cs') <- executeGF181 $ do
        x <- input Public :: Comp (UInt 2)
        y <- input Public :: Comp (UInt 2)
        performCLDivMod x y
      -- print _cs
      -- print cs'
      -- print $ linkConstraintModule cs'
      _cs `shouldHaveSize` 33
      cs' `shouldHaveSize` 20

  describe "Multiplication" $ do
    -- -- 8 * 3 for input / output
    -- -- 8 for carry bit
    -- -- 1 for multiplication
    -- it "2 variables / byte / GF181" $ do
    --   (cs, cs') <- executeGF181 $ do
    --     x <- inputUInt @8 Public
    --     y <- inputUInt @8 Public
    --     return $ x * y
    --   cs `shouldHaveSize` 42
    --   cs' `shouldHaveSize` 33

    -- TODO: can be lower
    it "variable / constant" $ do
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @4 Public
        return $ x * 4

      -- print cs
      -- print cs'
      -- debug cs'

      cs `shouldHaveSize` 18
      cs' `shouldHaveSize` 13
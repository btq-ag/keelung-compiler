{-# LANGUAGE DataKinds #-}

-- {-# LANGUAGE TypeApplications #-}

module Test.Optimization.UInt.CLDivMod (tests, run) where

import Keelung
-- import Keelung.Compiler.Linker

import Test.Hspec
import Test.Optimization.Util

-- --
run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Carry-less Div/Mod" $ do
  it "2 variables / 2-bit" $ do
    -- constraint breakdown:
    -- I/O: 8 = 2 * 4
    -- multiplication: 4 = 3 + 1
    -- remainder addition: 2
    -- divisor non-zero: 1
    -- divisor > remainder: 3

    (_cs2, cs2') <- executeGF181 $ do
      x <- input Public :: Comp (UInt 2)
      y <- input Public :: Comp (UInt 2)
      performCLDivMod x y
    _cs2 `shouldHaveSize` 33
    -- should be just 18
    cs2' `shouldHaveSize` 28
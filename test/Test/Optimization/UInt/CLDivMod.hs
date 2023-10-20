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
    (_cs, cs') <- executeGF181 $ do
      x <- input Public :: Comp (UInt 2)
      y <- input Public :: Comp (UInt 2)
      performCLDivMod x y
    -- print _cs
    -- print cs'
    -- print $ linkConstraintModule cs'
    _cs `shouldHaveSize` 33
    cs' `shouldHaveSize` 20
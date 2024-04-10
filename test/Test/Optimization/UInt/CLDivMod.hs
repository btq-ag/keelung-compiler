{-# LANGUAGE DataKinds #-}

-- {-# LANGUAGE TypeApplications #-}

module Test.Optimization.UInt.CLDivMod (tests, run) where

import Keelung
-- import Keelung.Compiler.Linker

import Test.Util
import Test.Hspec

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
    let program = do
          x <- input Public :: Comp (UInt 2)
          y <- input Public :: Comp (UInt 2)
          performCLDivMod x y
    assertCountO0 gf181 program 33
    assertCount gf181 program 28
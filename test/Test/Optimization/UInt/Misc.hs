{-# LANGUAGE DataKinds #-}

module Test.Optimization.UInt.Misc (tests, run) where

import Keelung
-- import Keelung.Compiler.Linker

import Test.Util
import Test.Hspec

-- --
run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Misc" $ do
  describe "AES Multiplication" $ do
    -- constraint breakdown:
    --  I/O: 8*2 = 16
    --  var eq: 1*5 = 5
    --  xor 2: 1*3 = 3
    it "constant 2" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            return $ x `aesMul` 2

      assertCountO0 gf181 program 27
      assertCount gf181 program 24
    -- constraint breakdown:
    --  I/O: 8*2 = 16
    --  var eq: 1*3 = 3
    --  xor 2: 1*4 = 4
    --  xor 3: 2*1 = 2
    it "constant 4" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            return $ x `aesMul` 4
      assertCountO0 gf181 program 30
      assertCount gf181 program 25
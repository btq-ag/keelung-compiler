{-# LANGUAGE DataKinds #-}

module Test.Optimization.UInt.AESMul (tests, run) where

import Keelung
-- import Keelung.Compiler.Linker
import Test.Hspec
import Test.Optimization.Util

-- --
run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "AES Multiplication" $ do
  -- constraint breakdown:
  --  I/O: 8*2 = 16
  --  var eq: 1*5 = 5
  --  xor 2: 1*3 = 3
  it "variable / constant = 2" $ do
    (cs, cs') <- executeGF181 $ do
      x <- input Public :: Comp (UInt 8)
      return $ x `aesMul` 2

    cs `shouldHaveSize` 27
    cs' `shouldHaveSize` 24
  -- constraint breakdown:
  --  I/O: 8*2 = 16
  --  var eq: 1*3 = 3
  --  xor 2: 1*4 = 4
  --  xor 3: 2*1 = 2
  it "variable / constant = 4" $ do
    (cs, cs') <- executeGF181 $ do
      x <- input Public :: Comp (UInt 8)
      return $ x `aesMul` 4

    cs `shouldHaveSize` 30
    cs' `shouldHaveSize` 25

  -- constraint breakdown:
  --  I/O: 8*3 = 24
  --  products: 64
  --  xor sum: 8
  --  odd/even: 4 + 5 * 7
  it "2 variables" $ do
    (cs, cs') <- executeGF181 $ do
      x <- input Public :: Comp (UInt 8)
      y <- input Public
      return $ x `aesMul` y

    cs `shouldHaveSize` 143
    cs' `shouldHaveSize` 143
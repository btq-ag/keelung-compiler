{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

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
  describe "AES Multiplication" $ do
    -- constraint breakdown:
    --  I/O: 8*2 = 16
    --  var eq: 1*5 = 5
    --  xor 2: 1*3 = 3
    it "constant 2" $ do
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @8 Public
        return $ x `aesMul` 2

      cs `shouldHaveSize` 27
      cs' `shouldHaveSize` 24
    -- constraint breakdown:
    --  I/O: 8*2 = 16
    --  var eq: 1*3 = 3
    --  xor 2: 1*4 = 4
    --  xor 3: 2*1 = 2
    it "constant 4" $ do
      (cs, cs') <- executeGF181 $ do
        x <- inputUInt @8 Public
        return $ x `aesMul` 4

      cs `shouldHaveSize` 30
      cs' `shouldHaveSize` 25
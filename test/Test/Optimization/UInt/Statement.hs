{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use head" #-}

module Test.Optimization.UInt.Statement (tests, run) where

import Keelung
-- import Keelung.Compiler.Linker

import Test.Util
import Test.Hspec

-- --
run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Statement" $ do
  describe "fromBools" $ do
    -- constraint breakdown:
    --  I/O: 8*2 = 16
    --  equality = ⌈ 8 / fieldWidth ⌉
    it "from variables" $ do
      let program = do
            xs <- inputList Public 8
            x <- fromBools xs
            return (x :: UInt 8)
      assertCountO0 gf181 program 26
      assertCount gf181 program 17

    it "bit tests" $ do
      let program = do
            xs <- inputList Public 8
            x <- fromBools [xs !! 0, xs !! 2, xs !! 4, xs !! 6, xs !! 1, xs !! 3, xs !! 5, xs !! 7]
            return (x :: UInt 8)
      assertCountO0 gf181 program 26
      assertCount gf181 program 17
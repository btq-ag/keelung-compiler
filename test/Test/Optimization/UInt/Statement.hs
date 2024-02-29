{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use head" #-}

module Test.Optimization.UInt.Statement (tests, run) where

import Keelung
-- import Keelung.Compiler.Linker
import Test.Hspec
import Test.Optimization.Util

-- --
run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Statement" $ do
  describe "fromBools" $ do
    -- constraint breakdown:
    --  I/O: 8*2 = 16
    --  equality = 8
    it "from variables" $ do
      (cs, cs') <- executeGF181 $ do
        xs <- inputList Public 8
        x <- fromBools xs
        return (x :: UInt 8)
      cs `shouldHaveSize` 33
      cs' `shouldHaveSize` 24

    it "bit tests" $ do
      (cs, cs') <- executeGF181 $ do
        xs <- inputList Public 8
        x <- fromBools [xs !! 0, xs !! 2, xs !! 4, xs !! 6, xs !! 1, xs !! 3, xs !! 5, xs !! 7]
        return (x :: UInt 8)
      cs `shouldHaveSize` 33
      cs' `shouldHaveSize` 24

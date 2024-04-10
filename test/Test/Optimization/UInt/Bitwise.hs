{-# LANGUAGE DataKinds #-}

module Test.Optimization.UInt.Bitwise (tests, run) where

import Keelung
-- import Keelung.Compiler.Linker
import Test.Hspec
import Test.Optimization.Util

-- --
run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Bitwise" $ do
  describe "Shifts" $ do
    it "left" $ do
      (_cs, _cs') <- executeGF181 $ do
        x <- input Public :: Comp (UInt 8)
        return $ x .<<. 1
      -- print _cs
      -- print cs'
      -- print $ linkConstraintModule cs'
      debugM _cs

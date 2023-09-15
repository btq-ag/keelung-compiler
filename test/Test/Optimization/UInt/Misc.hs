{-# LANGUAGE DataKinds #-}

module Test.Optimization.UInt.Misc (tests, run) where

import Keelung
import Keelung.Compiler.Linker ()
import Test.Hspec
import Test.Optimization.Util

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Misc" $ do
  -- can be lower
  it "REMOVE WRITEQU" $ do
    (cs, cs') <- executeGF181 $ do
      input Private :: Comp (UInt 8)
    -- print cs
    -- print $ linkConstraintModule cs
    cs `shouldHaveSize` 17
    cs' `shouldHaveSize` 17

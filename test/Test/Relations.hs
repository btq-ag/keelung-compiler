{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Relations (tests, run) where

import Test.Hspec
import Test.Relations.Reference qualified as Relations.Reference
import Test.Relations.Slice qualified as Relations.Slice

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Compilation against witness solver" $ do
  Relations.Reference.tests

-- Relations.Slice.tests

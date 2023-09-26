module Test.Relations (tests, run) where

import Test.Hspec
import Test.Relations.Boolean qualified as Relations.Boolean
import Test.Relations.Field qualified as Relations.Field

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Compilation against witness solver" $ do
  Relations.Field.tests
  Relations.Boolean.tests

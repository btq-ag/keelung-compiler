module Test.Compilation (tests, run) where

import Test.Compilation.Boolean qualified
import Test.Compilation.Field qualified
import Test.Compilation.Misc qualified
import Test.Compilation.UInt qualified
import Test.Hspec

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "Compilation against witness solver" $ do
    Test.Compilation.Field.tests
    Test.Compilation.Boolean.tests
    Test.Compilation.UInt.tests
    Test.Compilation.Misc.tests

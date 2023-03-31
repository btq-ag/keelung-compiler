module Test.Interpreter (tests, run) where

import Test.Hspec
import Test.Interpreter.Boolean qualified
import Test.Interpreter.Field qualified
import Test.Interpreter.Misc qualified
import Test.Interpreter.UInt qualified

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "Interpreter against witness generation" $ do
    Test.Interpreter.Field.tests
    Test.Interpreter.Boolean.tests
    Test.Interpreter.UInt.tests
    Test.Interpreter.Misc.tests

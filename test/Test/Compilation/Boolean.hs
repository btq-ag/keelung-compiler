module Test.Compilation.Boolean (tests, run) where

import Control.Monad
import Keelung hiding (compile)
import Test.Compilation.Boolean.Conditional qualified
import Test.Compilation.Boolean.Equality qualified
import Test.Compilation.Boolean.Inequality qualified
import Test.Compilation.Boolean.Logical qualified
import Test.Compilation.Util
import Test.Hspec

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Boolean" $ do
  Test.Compilation.Boolean.Logical.tests
  Test.Compilation.Boolean.Equality.tests
  Test.Compilation.Boolean.Inequality.tests
  Test.Compilation.Boolean.Conditional.tests

  describe "conversion to Field" $ do
    it "BtoF" $ do
      let program = do
            x <- input Public
            return $ BtoF x
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [1] [] [1]
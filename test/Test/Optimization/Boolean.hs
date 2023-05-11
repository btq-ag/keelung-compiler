module Test.Optimization.Boolean (tests, run) where

import Keelung hiding (compileO0)
import Test.Hspec
import Test.Optimization.Util

tests :: SpecWith ()
tests = do
  describe "Boolean" $ do
    describe "xor" $ do
      it "variable / variable" $ do
        (cs, cs') <- execute $ do
          x <- inputBool Public
          y <- inputBool Public
          return $ x .^. y
        cs `shouldHaveSize` 5
        cs' `shouldHaveSize` 4

      it "variable / constant" $ do
        (cs, cs') <- execute $ do
          x <- inputBool Public
          return $ x .^. true
        cs `shouldHaveSize` 3
        cs' `shouldHaveSize` 3

      it "constant / variable" $ do
        (cs, cs') <- execute $ do
          x <- inputBool Public
          return $ false .^. x
        cs `shouldHaveSize` 3
        cs' `shouldHaveSize` 3

      it "constant / constant" $ do
        (cs, cs') <- execute $ do
          return $ false .^. true
        cs `shouldHaveSize` 2
        cs' `shouldHaveSize` 2

--------------------------------------------------------------------------------

run :: IO ()
run = hspec tests

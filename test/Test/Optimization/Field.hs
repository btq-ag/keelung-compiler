module Test.Optimization.Field (tests, run) where

import Keelung hiding (compileO0)
import Test.Hspec
import Test.Optimization.Util (executeGF181, shouldHaveSize)

tests :: SpecWith ()
tests = do
  describe "Field" $ do
      -- 1
      it "x `pow` 0" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputField Public
          return $ x `pow` 0
        cs `shouldHaveSize` 1
        cs' `shouldHaveSize` 1
      
      -- ((x ^ 2) ^ 2) * x
      it "x `pow` 5" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputField Public
          return $ x `pow` 5
        cs `shouldHaveSize` 5
        cs' `shouldHaveSize` 3
      
      -- ((((x ^ 2) * x) ^ 2) ^ 2) * x
      it "x `pow` 13" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputField Public
          return $ x `pow` 13
        cs `shouldHaveSize` 7
        cs' `shouldHaveSize` 5

--------------------------------------------------------------------------------

run :: IO ()
run = hspec tests

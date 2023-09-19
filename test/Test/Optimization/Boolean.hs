module Test.Optimization.Boolean (tests, run) where

import Keelung hiding (compileO0)
import Test.Hspec
import Test.Optimization.Util

tests :: SpecWith ()
tests = do
  describe "Boolean" $ do
    describe "and" $ do
      it "variable / variable" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputBool Public
          y <- inputBool Public
          return $ x .&. y
        cs `shouldHaveSize` 5
        cs' `shouldHaveSize` 4

      it "variable / constant" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputBool Public
          return $ x .&. true
        cs `shouldHaveSize` 3
        cs' `shouldHaveSize` 3

      it "constant / constant" $ do
        (cs, cs') <- executeGF181 $ do
          return $ false .&. true
        cs `shouldHaveSize` 2
        cs' `shouldHaveSize` 2

      it "3 operands" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputBool Public
          y <- inputBool Public
          z <- inputBool Public
          return $ x .&. y .&. z
        cs `shouldHaveSize` 7
        cs' `shouldHaveSize` 6

      it "4 operands" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputBool Public
          y <- inputBool Public
          z <- inputBool Public
          w <- inputBool Public
          return $ x .&. y .&. z .&. w
        cs `shouldHaveSize` 8
        cs' `shouldHaveSize` 7

    describe "or" $ do
      it "variable / variable" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputBool Public
          y <- inputBool Public
          return $ x .|. y
        cs `shouldHaveSize` 5
        cs' `shouldHaveSize` 4

      it "variable / constant" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputBool Public
          return $ x .|. true
        cs `shouldHaveSize` 3
        cs' `shouldHaveSize` 3

      it "constant / constant" $ do
        (cs, cs') <- executeGF181 $ do
          return $ false .|. true
        cs `shouldHaveSize` 2
        cs' `shouldHaveSize` 2

      it "3 operands" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputBool Public
          y <- inputBool Public
          z <- inputBool Public
          return $ x .|. y .|. z
        cs `shouldHaveSize` 7
        cs' `shouldHaveSize` 6

      it "4 operands" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputBool Public
          y <- inputBool Public
          z <- inputBool Public
          w <- inputBool Public
          return $ x .|. y .|. z .|. w
        cs `shouldHaveSize` 8
        cs' `shouldHaveSize` 7

    describe "xor" $ do
      it "variable / variable" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputBool Public
          y <- inputBool Public
          return $ x .^. y
        cs `shouldHaveSize` 5
        cs' `shouldHaveSize` 4

      it "variable / constant" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputBool Public
          return $ x .^. true
        cs `shouldHaveSize` 3
        cs' `shouldHaveSize` 3

      it "constant / variable" $ do
        (cs, cs') <- executeGF181 $ do
          x <- inputBool Public
          return $ false .^. x
        cs `shouldHaveSize` 3
        cs' `shouldHaveSize` 3

      it "constant / constant" $ do
        (cs, cs') <- executeGF181 $ do
          return $ false .^. true
        cs `shouldHaveSize` 2
        cs' `shouldHaveSize` 2

      it "2 variables" $ do
        (cs, cs') <- executeGF181 $ do
          xs <- inputList Public 2 :: Comp [Boolean]
          return $ foldl (.^.) false xs
        cs `shouldHaveSize` 5
        cs' `shouldHaveSize` 4

      it "10 variables" $ do
        (cs, cs') <- executeGF181 $ do
          xs <- inputList Public 10 :: Comp [Boolean]
          return $ foldl (.^.) false xs
        cs `shouldHaveSize` 13
        cs' `shouldHaveSize` 12

--------------------------------------------------------------------------------

run :: IO ()
run = hspec tests

module Test.Optimization.Boolean (tests, run) where

import Keelung hiding (compileO0)
import Test.Util
import Test.Hspec

tests :: SpecWith ()
tests = do
  describe "Boolean" $ do
    describe "and" $ do
      it "variable / variable" $ do
        let program = do
              x <- inputBool Public
              y <- inputBool Public
              return $ x .&. y
        assertCountO0 gf181 program 5
        assertCount gf181 program 4

      it "variable / constant" $ do
        let program = do
              x <- inputBool Public
              return $ x .&. true
        assertCountO0 gf181 program 3
        assertCount gf181 program 3

      it "constant / constant" $ do
        let program = do
              return $ false .&. true
        assertCountO0 gf181 program 2
        assertCount gf181 program 2

      it "3 operands" $ do
        let program = do
              x <- inputBool Public
              y <- inputBool Public
              z <- inputBool Public
              return $ x .&. y .&. z
        assertCountO0 gf181 program 7
        assertCount gf181 program 6

      it "4 operands" $ do
        let program = do
              x <- inputBool Public
              y <- inputBool Public
              z <- inputBool Public
              w <- inputBool Public
              return $ x .&. y .&. z .&. w
        assertCountO0 gf181 program 8
        assertCount gf181 program 7

    describe "or" $ do
      it "variable / variable" $ do
        let program = do
              x <- inputBool Public
              y <- inputBool Public
              return $ x .|. y
        assertCountO0 gf181 program 5
        assertCount gf181 program 4

      it "variable / constant" $ do
        let program = do
              x <- inputBool Public
              return $ x .|. true
        assertCountO0 gf181 program 3
        assertCount gf181 program 3

      it "constant / constant" $ do
        let program = do
              return $ false .|. true
        assertCountO0 gf181 program 2
        assertCount gf181 program 2

      it "3 operands" $ do
        let program = do
              x <- inputBool Public
              y <- inputBool Public
              z <- inputBool Public
              return $ x .|. y .|. z
        assertCountO0 gf181 program 7
        assertCount gf181 program 6

      it "4 operands" $ do
        let program = do
              x <- inputBool Public
              y <- inputBool Public
              z <- inputBool Public
              w <- inputBool Public
              return $ x .|. y .|. z .|. w
        assertCountO0 gf181 program 8
        assertCount gf181 program 7

    describe "xor" $ do
      it "variable / variable" $ do
        let program = do
              x <- inputBool Public
              y <- inputBool Public
              return $ x .^. y
        assertCountO0 gf181 program 5
        assertCount gf181 program 4

      it "variable / constant" $ do
        let program = do
              x <- inputBool Public
              return $ x .^. true
        assertCountO0 gf181 program 3
        assertCount gf181 program 3

      it "constant / variable" $ do
        let program = do
              x <- inputBool Public
              return $ false .^. x
        assertCountO0 gf181 program 3
        assertCount gf181 program 3

      it "constant / constant" $ do
        let program = do
              return $ false .^. true
        assertCountO0 gf181 program 2
        assertCount gf181 program 2

      it "1 variable" $ do
        let program = do
              xs <- inputList Public 1 :: Comp [Boolean]
              return $ foldl (.^.) false xs
        assertCountO0 gf181 program 3
        assertCount gf181 program 3

      it "2 variables" $ do
        let program = do
              xs <- inputList Public 2 :: Comp [Boolean]
              return $ foldl (.^.) false xs
        assertCountO0 gf181 program 5
        assertCount gf181 program 4 -- 3 + 1
      it "3 variables" $ do
        let program = do
              xs <- inputList Public 3 :: Comp [Boolean]
              return $ foldl (.^.) false xs
        assertCountO0 gf181 program 7
        assertCount gf181 program 6 -- 4 + 2
    it "4 variables" $ do
      let program = do
            xs <- inputList Public 4 :: Comp [Boolean]
            return $ foldl (.^.) false xs
      assertCountO0 gf181 program 9
      assertCount gf181 program 8

    -- TODO: should be just 9
    it "5 variables" $ do
      let program = do
            xs <- inputList Public 5 :: Comp [Boolean]
            return $ foldl (.^.) false xs
      assertCountO0 gf181 program 11
      assertCount gf181 program 11

    it "10 variables" $ do
      let program = do
            xs <- inputList Public 10 :: Comp [Boolean]
            return $ foldl (.^.) false xs
      assertCountO0 gf181 program 17
      assertCount gf181 program 17

--------------------------------------------------------------------------------

run :: IO ()
run = hspec tests

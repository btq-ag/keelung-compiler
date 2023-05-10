module Test.Interpreter.Field (tests, run) where

import Keelung hiding (compile, run)
import Test.Hspec
import Test.Interpreter.Util
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Field" $ do
  it "arithmetics 1" $ do
    let program = do
          x <- inputField Public
          y <- inputField Public
          return $ x * y + y * 2
    property $ \(x, y) -> do
      runAll program [x, y :: GF181] [] [x * y + y * 2]

  it "arithmetics 2" $ do
    let program = do
          x <- inputField Public
          y <- inputField Private
          z <- reuse $ x * y + y * 2
          return $ x * y - z
    property $ \(x, y) -> do
      runAll program [x :: GF181] [y] [-y * 2]

  it "arithmetics 3" $ do
    let program = do
          x <- inputField Private
          y <- inputField Public
          let z = 3
          return $ x * z + y * 2
    
    property $ \(x, y) -> do
      runAll program [y :: GF181] [x] [x * 3 + y * 2]

  it "summation" $ do
    let program = do
          arr <- inputList Public 4
          reduce 0 [0 .. 3] $ \accum i -> do
            let x = arr !! i
            return (accum + x :: Field)

    forAll (vector 4) $ \xs -> do
      runAll program (xs :: [GF181]) [] [sum xs]

  it "eq 1" $ do
    -- takes an input and see if its equal to 3
    let program = do
          x <- inputField Public
          return $ x `eq` 3

    property $ \x -> do
      let expectedOutput = if x == 3 then [1] else [0]
      runAll program [x :: GF181] [] expectedOutput

  it "conditional" $ do
    let program = do
          x <- inputField Public
          return $ cond (x `eq` 3) 4 (5 :: Field)
    property $ \x -> do
      let expectedOutput = if x == 3 then [4] else [5]
      runAll program [x :: GF181] [] expectedOutput

module Test.Interpreter.Field (tests, run) where

import Control.Monad
import Keelung hiding (compile)
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
      runAll gf181Info program [toInteger x, toInteger y] [] [x * y + y * 2 :: GF181]

  it "arithmetics 2" $ do
    let program = do
          x <- inputField Public
          y <- inputField Private
          z <- reuse $ x * y + y * 2
          return $ x * y - z
    property $ \(x, y) -> do
      runAll gf181Info program [x] [toInteger y] [-y * 2 :: GF181]

  it "arithmetics 3" $ do
    let program = do
          x <- inputField Private
          y <- inputField Public
          let z = 3
          return $ x * z + y * 2

    property $ \(x, y) -> do
      runAll gf181Info program [toInteger y] [toInteger x] [x * 3 + y * 2 :: GF181]

  it "summation" $ do
    let program = do
          arr <- inputList Public 4
          reduce 0 [0 .. 3] $ \accum i -> do
            let x = arr !! i
            return (accum + x :: Field)

    forAll (vector 4) $ \xs -> do
      runAll gf181Info program (map toInteger xs) [] [sum xs :: GF181]

  it "eq (variable / variable)" $ do
    let program = do
          x <- inputField Public
          y <- inputField Public
          return $ x `eq` y
    property $ \(x', y') -> do
      let x = x' `mod` 4
          y = y' `mod` 4
      let expectedOutput = if x == y then [1 :: GF181] else [0]
      runAll gf181Info program [x, y] [] expectedOutput

  it "eq (variable / constant)" $ do
    let program y = do
          x <- inputField Public
          return $ x `eq` fromInteger y
    property $ \(x', y') -> do
      let x = x' `mod` 4
          y = y' `mod` 4
      let expectedOutput = if x == y then [1 :: GF181] else [0]
      runAll gf181Info (program y) [fromInteger x] [] expectedOutput

  it "eq (constant / constant)" $ do
    let program x y = do
          return $ fromInteger x `eq` (fromInteger y :: Field)

    property $ \(x', y') -> do
      let x = x' `mod` 4
          y = y' `mod` 4
      let expectedOutput = if x == y then [1 :: GF181] else [0]
      runAll gf181Info (program x y) [] [] expectedOutput

  it "conditional (variable)" $ do
    let program = do
          x <- inputBool Public
          y <- inputField Public
          return $ cond x y (5 :: Field)

    property $ \(x', y') -> do
      let x = x' `mod` 4
          y = y' `mod` 4
      let expectedOutput = if (x `mod` 2) == 1 then [y :: GF181] else [5]
      runAll gf181Info program [x `mod` 2, toInteger y] [] expectedOutput

  it "exponentiation (variable base)" $ do
    let program i = do
          x <- inputField Public
          return (x `pow` i)
    property $ \(x, i) -> do
      when (i >= 0) $ do
        let expectedOutput = [x ^ (i :: Integer) :: GF181]
        runAll gf181Info (program i) [toInteger x] [] expectedOutput

  it "exponentiation (constant base)" $ do
    let program x i = do
          return (fromIntegral x `pow` i)
    property $ \(x, i) -> do
      when (i >= 0) $ do
        let expectedOutput = [x ^ (i :: Integer)]
        runAll gf181Info (program (x :: GF181) i) [] [] expectedOutput

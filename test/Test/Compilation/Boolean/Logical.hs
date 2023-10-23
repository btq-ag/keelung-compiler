module Test.Compilation.Boolean.Logical (tests, run) where

import Control.Monad
import Data.Bits qualified
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "logical" $ do
  describe "complement" $ do
    it "constant true" $ do
      let program = return $ complement true
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [] [] [0]

    it "constant false" $ do
      let program = return $ complement false
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [] [] [1]

    it "variable" $ do
      let program = complement <$> inputBool Public
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [0] [] [1]
        runAll field program [1] [] [0]

  describe "conjunction" $ do
    it "variable + constant true" $ do
      let program = (.&.) true <$> inputBool Public
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [0] [] [0]
        runAll field program [1] [] [1]

    it "variable + constant false" $ do
      let program = (.&.) false <$> inputBool Public
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [0] [] [0]
        runAll field program [1] [] [0]

    it "2 variables" $ do
      let program = (.&.) <$> inputBool Public <*> inputBool Public
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [0, 0] [] [0]
        runAll field program [0, 1] [] [0]
        runAll field program [1, 0] [] [0]
        runAll field program [1, 1] [] [1]

    it "3 variables" $ do
      let program = (.&.) <$> ((.&.) <$> inputBool Public <*> inputBool Public) <*> inputBool Public
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [0, 0, 0] [] [0]
        runAll field program [0, 0, 1] [] [0]
        runAll field program [0, 1, 0] [] [0]
        runAll field program [0, 1, 1] [] [0]
        runAll field program [1, 0, 0] [] [0]
        runAll field program [1, 0, 1] [] [0]
        runAll field program [1, 1, 0] [] [0]
        runAll field program [1, 1, 1] [] [1]

    it "more than 3 variables + constant" $ do
      let program constant n = do
            xs <- replicateM n (inputBool Public)
            return $ foldl (.|.) (if constant then true else false) xs
      forAll
        ( do
            n <- choose (4, 20)
            xs <- replicateM n (choose (0, 1))
            constant <- arbitrary
            return (n, constant, xs)
        )
        $ \(n, constant, xs) -> do
          let expected = [foldl (Data.Bits..|.) (if constant then 1 else 0) xs]
          forM_ [gf181, Prime 2, Binary 7] $ \field -> do
            runAll field (program constant n) xs [] expected

  describe "disjunction" $ do
    it "variable + constant true" $ do
      let program = (.|.) true <$> inputBool Public
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [0] [] [1]
        runAll field program [1] [] [1]

    it "variable + constant false" $ do
      let program = (.|.) false <$> inputBool Public
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [0] [] [0]
        runAll field program [1] [] [1]

    it "2 variables" $ do
      let program = (.|.) <$> inputBool Public <*> inputBool Public
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [0, 0] [] [0]
        runAll field program [0, 1] [] [1]
        runAll field program [1, 0] [] [1]
        runAll field program [1, 1] [] [1]

    it "3 variables" $ do
      let program = (.|.) <$> ((.|.) <$> inputBool Public <*> inputBool Public) <*> inputBool Public
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [0, 0, 0] [] [0]
        runAll field program [0, 0, 1] [] [1]
        runAll field program [0, 1, 0] [] [1]
        runAll field program [0, 1, 1] [] [1]
        runAll field program [1, 0, 0] [] [1]
        runAll field program [1, 0, 1] [] [1]
        runAll field program [1, 1, 0] [] [1]
        runAll field program [1, 1, 1] [] [1]

    it "more than 3 variables + constant" $ do
      let program constant n = do
            xs <- replicateM n (inputBool Public)
            return $ foldl (.&.) (if constant then true else false) xs
      forAll
        ( do
            n <- choose (4, 20)
            xs <- replicateM n (choose (0, 1))
            constant <- arbitrary
            return (n, constant, xs)
        )
        $ \(n, constant, xs) -> do
          let expected = [foldl (Data.Bits..&.) (if constant then 1 else 0) xs]
          forM_ [gf181, Prime 2, Binary 7] $ \field -> do
            runAll field (program constant n) xs [] expected

  describe "exclusive disjunction" $ do
    it "variable + constant true" $ do
      let program = (.^.) true <$> inputBool Public
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [0] [] [1]
        runAll field program [1] [] [0]

    it "variable + constant false" $ do
      let program = (.^.) false <$> inputBool Public
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [0] [] [0]
        runAll field program [1] [] [1]

    it "2 variables" $ do
      let program = (.^.) <$> inputBool Public <*> inputBool Public
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [0, 0] [] [0]
        runAll field program [0, 1] [] [1]
        runAll field program [1, 0] [] [1]
        runAll field program [1, 1] [] [0]

    it "4 variables" $ do
      let program = (.^.) <$> ((.^.) <$> ((.^.) <$> inputBool Public <*> inputBool Public) <*> inputBool Public) <*> inputBool Public
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [0, 0, 0, 0] [] [0]
        runAll field program [0, 0, 0, 1] [] [1]
        runAll field program [0, 0, 1, 0] [] [1]
        runAll field program [0, 0, 1, 1] [] [0]
        runAll field program [0, 1, 0, 0] [] [1]
        runAll field program [0, 1, 0, 1] [] [0]
        runAll field program [0, 1, 1, 0] [] [0]
        runAll field program [0, 1, 1, 1] [] [1]
        runAll field program [1, 0, 0, 0] [] [1]
        runAll field program [1, 0, 0, 1] [] [0]
        runAll field program [1, 0, 1, 0] [] [0]
        runAll field program [1, 0, 1, 1] [] [1]
        runAll field program [1, 1, 0, 0] [] [0]
        runAll field program [1, 1, 0, 1] [] [1]
        runAll field program [1, 1, 1, 0] [] [1]
        runAll field program [1, 1, 1, 1] [] [0]

    it "more than 4 variables + constant" $ do
      let program constant n = do
            xs <- replicateM n (inputBool Public)
            return $ foldl (.^.) (if constant then true else false) xs
      forAll
        ( do
            n <- choose (5, 20)
            xs <- replicateM n (choose (0, 1))
            constant <- arbitrary
            return (n, constant, xs)
        )
        $ \(n, constant, xs) -> do
          let expected = [foldl Data.Bits.xor (if constant then 1 else 0) xs]
          forM_ [gf181, Prime 2, Prime 13, Prime 257, Binary 7] $ \field -> do
            runAll field (program constant n) xs [] expected

  it "mixed 1" $ do
    let program = do
          x <- input Public
          y <- input Private
          let z = true
          return $ x `Or` y `And` z
    forM_ [gf181, Prime 2, Binary 7] $ \field -> do
      runAll field program [0] [0] [0]
      runAll field program [0] [1] [1]
      runAll field program [1] [0] [1]
      runAll field program [1] [1] [1]

  it "mixed 2" $ do
    let program = do
          x <- input Public
          y <- input Private
          let z = false
          w <- reuse $ x `Or` y
          return $ x `And` w `Or` z
    forM_ [gf181, Prime 2, Binary 7] $ \field -> do
      runAll field program [0] [0] [0]
      runAll field program [0] [1] [0]
      runAll field program [1] [0] [1]
      runAll field program [1] [1] [1]
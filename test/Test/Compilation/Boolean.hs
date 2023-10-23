module Test.Compilation.Boolean (tests, run) where

import Control.Monad
import Data.Bits qualified
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Boolean" $ do
  describe "complement" $ do
    it "constant true" $ do
      let program = return $ complement true
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
        runAll field program [] [] [0]

    it "constant false" $ do
      let program = return $ complement false
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
        runAll field program [] [] [1]

    it "variable" $ do
      let program = complement <$> inputBool Public
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
        runAll field program [0] [] [1]
        runAll field program [1] [] [0]

  describe "and" $ do
    it "variable + constant true" $ do
      let program = (.&.) true <$> inputBool Public
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
        runAll field program [0] [] [0]
        runAll field program [1] [] [1]

    it "variable + constant false" $ do
      let program = (.&.) false <$> inputBool Public
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
        runAll field program [0] [] [0]
        runAll field program [1] [] [0]

    it "2 variables" $ do
      let program = (.&.) <$> inputBool Public <*> inputBool Public
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
        runAll field program [0, 0] [] [0]
        runAll field program [0, 1] [] [0]
        runAll field program [1, 0] [] [0]
        runAll field program [1, 1] [] [1]

    it "3 variables" $ do
      let program = (.&.) <$> ((.&.) <$> inputBool Public <*> inputBool Public) <*> inputBool Public
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
        runAll field program [0, 0, 0] [] [0]
        runAll field program [0, 0, 1] [] [0]
        runAll field program [0, 1, 0] [] [0]
        runAll field program [0, 1, 1] [] [0]
        runAll field program [1, 0, 0] [] [0]
        runAll field program [1, 0, 1] [] [0]
        runAll field program [1, 1, 0] [] [0]
        runAll field program [1, 1, 1] [] [1]
  describe "or" $ do
    it "variable + constant true" $ do
      let program = (.|.) true <$> inputBool Public
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
        runAll field program [0] [] [1]
        runAll field program [1] [] [1]

    it "variable + constant false" $ do
      let program = (.|.) false <$> inputBool Public
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
        runAll field program [0] [] [0]
        runAll field program [1] [] [1]

    it "2 variables" $ do
      let program = (.|.) <$> inputBool Public <*> inputBool Public
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
        runAll field program [0, 0] [] [0]
        runAll field program [0, 1] [] [1]
        runAll field program [1, 0] [] [1]
        runAll field program [1, 1] [] [1]

    it "3 variables" $ do
      let program = (.|.) <$> ((.|.) <$> inputBool Public <*> inputBool Public) <*> inputBool Public
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
        runAll field program [0, 0, 0] [] [0]
        runAll field program [0, 0, 1] [] [1]
        runAll field program [0, 1, 0] [] [1]
        runAll field program [0, 1, 1] [] [1]
        runAll field program [1, 0, 0] [] [1]
        runAll field program [1, 0, 1] [] [1]
        runAll field program [1, 1, 0] [] [1]
        runAll field program [1, 1, 1] [] [1]

  describe "xor" $ do
    it "mixed" $ testProgram Data.Bits.xor Xor

    it "variable + constant true" $ do
      let program = (.^.) true <$> inputBool Public
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
        runAll field program [0] [] [1]
        runAll field program [1] [] [0]

    it "variable + constant false" $ do
      let program = (.^.) false <$> inputBool Public
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
        runAll field program [0] [] [0]
        runAll field program [1] [] [1]

    it "2 variables" $ do
      let program = (.^.) <$> inputBool Public <*> inputBool Public
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
        runAll field program [0, 0] [] [0]
        runAll field program [0, 1] [] [1]
        runAll field program [1, 0] [] [1]
        runAll field program [1, 1] [] [0]

    it "4 variables" $ do
      let program = (.^.) <$> ((.^.) <$> ((.^.) <$> inputBool Public <*> inputBool Public) <*> inputBool Public) <*> inputBool Public
      forM_ [gf181, Prime 2, Binary 5] $ \field -> do
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

    it "more than 2 variables" $ do
      let program n = do
            xs <- replicateM n (inputBool Public)
            return $ foldl (.^.) false xs
      forAll
        ( do
            n <- choose (8, 8)
            xs <- replicateM n (choose (0, 1))
            return (n, xs)
        )
        $ \(n, xs) -> do
          let expected = [foldl Data.Bits.xor 0 xs]
          forM_ [gf181, Prime 2, Prime 13, Prime 257, Binary 5] $ \field -> do
            runAll field (program n) xs [] expected

    it "2 variables with constant" $ do
      let program = do
            x <- inputBool Public
            y <- inputBool Public
            return $ x .^. y .^. true
      forAll
        ( do
            x <- choose (0, 1)
            y <- choose (0, 1)
            return (x, y)
        )
        $ \(x, y) -> do
          let expected = [x `Data.Bits.xor` y `Data.Bits.xor` 1]
          forM_ [gf181, Prime 2, Prime 13, Prime 257, Binary 5] $ \field -> do
            runAll field program [x, y] [] expected

    it "3 variables with constant" $ do
      let program = do
            x <- inputBool Public
            y <- inputBool Public
            z <- inputBool Public
            return $ x .^. y .^. z .^. true
      forAll
        ( do
            x <- choose (0, 1)
            y <- choose (0, 1)
            z <- choose (0, 1)
            return (x, y, z)
        )
        $ \(x, y, z) -> do
          let expected = [x `Data.Bits.xor` y `Data.Bits.xor` z `Data.Bits.xor` 1]
          forM_ [gf181, Prime 2, Prime 13, Prime 257, Binary 5] $ \field -> do
            runAll field program [x, y, z] [] expected

  it "mixed 1" $ do
    let program = do
          x <- input Public
          y <- input Private
          let z = true
          return $ x `Or` y `And` z
    runAll gf181 program [0] [0] [0]
    runAll gf181 program [0] [1] [1]
    runAll gf181 program [1] [0] [1]
    runAll gf181 program [1] [1] [1]

  it "mixed 2" $ do
    let program = do
          x <- input Public
          y <- input Private
          let z = false
          w <- reuse $ x `Or` y
          return $ x `And` w `Or` z
    runAll gf181 program [0] [0] [0]
    runAll gf181 program [0] [1] [0]
    runAll gf181 program [1] [0] [1]
    runAll gf181 program [1] [1] [1]

  it "eq 1" $ do
    -- takes an input and see if its equal to False
    let program = do
          x <- input Public
          return $ x `eq` false

    runAll gf181 program [0] [] [1]
    runAll gf181 program [1] [] [0]

  it "conditional" $ do
    let program = do
          x <- inputField Public
          return $ cond (x `eq` 3) true false
    property $ \x -> do
      let expectedOutput = if x == 3 then [1] else [0]
      runAll gf181 program [x] [] expectedOutput

  it "BtoF" $ do
    let program = do
          x <- input Public
          y <- input Private
          return $ BtoF x * BtoF y
    runAll gf181 program [1] [1] [1]

--------------------------------------------------------------------------------

fromBool :: Bool -> Integer
fromBool True = 1
fromBool False = 0

makeProgram :: (Boolean -> Boolean -> Boolean) -> Int -> Boolean -> Boolean -> [Boolean] -> Comp Boolean
makeProgram op mode a b cs = case mode `mod` 4 of
  0 -> do
    x <- inputBool Public
    y <- inputBool Public
    return $ foldl op (x `op` y) cs
  1 -> do
    y <- inputBool Public
    return $ foldl op (a `op` y) cs
  2 -> do
    x <- inputBool Public
    return $ foldl op (x `op` b) cs
  _ -> do
    return $ foldl op (a `op` b) cs

testProgram :: (Bool -> Bool -> Bool) -> (Boolean -> Boolean -> Boolean) -> Property
testProgram opH opK = do
  property $ \(mode, a, b, cs) -> do
    let expectedOutput = [fromInteger (fromBool (foldl opH (a `opH` b) cs))]
    let inputs = case mode `mod` 4 of
          0 -> [fromBool a, fromBool b]
          1 -> [fromBool b]
          2 -> [fromBool a]
          _ -> []
    runAll gf181 (makeProgram opK (mode `mod` 4 :: Int) (Boolean a) (Boolean b) (map Boolean cs)) inputs [] expectedOutput
    runAll (Binary 5) (makeProgram opK (mode `mod` 4 :: Int) (Boolean a) (Boolean b) (map Boolean cs)) inputs [] expectedOutput

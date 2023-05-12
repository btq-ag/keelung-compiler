module Test.Interpreter.Boolean (tests, run) where

import Data.Bits qualified
import Keelung hiding (compile)
import Test.Hspec
import Test.Interpreter.Util
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

toGF181 :: Bool -> GF181
toGF181 True = 1
toGF181 False = 0

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
    let expectedOutput = [toGF181 (foldl opH (a `opH` b) cs)]
    let inputs = case mode `mod` 4 of
          0 -> [toGF181 a, toGF181 b]
          1 -> [toGF181 b]
          2 -> [toGF181 a]
          _ -> []
    runAll gf181Info (makeProgram opK (mode `mod` 4 :: Int) (Boolean a) (Boolean b) (map Boolean cs)) inputs ([] :: [GF181]) expectedOutput

tests :: SpecWith ()
tests = describe "Boolean" $ do
  it "not 1" $ do
    let program = return $ complement true
    runAll gf181Info program [] [] [0 :: GF181]

  it "not 2" $ do
    let program = complement <$> inputBool Public
    runAll gf181Info program [0] [] [1 :: GF181]
    runAll gf181Info program [1] [] [0 :: GF181]

  it "and" $ testProgram (&&) And
  it "or" $ testProgram (||) Or
  it "xor" $ testProgram Data.Bits.xor Xor

  it "mixed 1" $ do
    let program = do
          x <- input Public
          y <- input Private
          let z = true
          return $ x `Or` y `And` z
    runAll gf181Info program [0] [0] [0 :: GF181]
    runAll gf181Info program [0] [1] [1 :: GF181]
    runAll gf181Info program [1] [0] [1 :: GF181]
    runAll gf181Info program [1] [1] [1 :: GF181]

  it "mixed 2" $ do
    let program = do
          x <- input Public
          y <- input Private
          let z = false
          w <- reuse $ x `Or` y
          return $ x `And` w `Or` z
    runAll gf181Info program [0] [0] [0 :: GF181]
    runAll gf181Info program [0] [1] [0 :: GF181]
    runAll gf181Info program [1] [0] [1 :: GF181]
    runAll gf181Info program [1] [1] [1 :: GF181]

  it "eq 1" $ do
    -- takes an input and see if its equal to False
    let program = do
          x <- input Public
          return $ x `eq` false

    runAll gf181Info program [0] [] [1 :: GF181]
    runAll gf181Info program [1] [] [0 :: GF181]

  it "conditional" $ do
    let program = do
          x <- inputField Public
          return $ cond (x `eq` 3) true false
    property $ \x -> do
      let expectedOutput = if x == 3 then [1] else [0]
      runAll gf181Info program [x :: GF181] [] expectedOutput

  it "BtoF" $ do
    let program = do
          x <- input Public
          y <- input Private
          return $ BtoF x * BtoF y
    runAll gf181Info program [1 :: GF181] [1] [1]

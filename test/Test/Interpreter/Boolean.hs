module Test.Interpreter.Boolean (tests, run) where

import Keelung hiding (compile, run)
import Test.Hspec
import Test.Interpreter.Util
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Boolean" $ do
  -- it "not 1" $ do
  --   let program = return $ complement true
  --   runAll program [] [] [0 :: GF181]

  -- it "not 2" $ do
  --   let program = complement <$> inputBool Public
  --   runAll program [0] [] [1 :: GF181]
  --   runAll program [1] [] [0 :: GF181]

  -- it "and 1" $ do
  --   let program = return $ true `And` false
  --   runAll program [] [] [0 :: GF181]

  -- it "and 2" $ do
  --   let program = And <$> input Public <*> input Private
  --   runAll program [1] [0] [0 :: GF181]
  --   runAll program [1] [1] [1 :: GF181]
  --   runAll program [0] [1] [0 :: GF181]
  --   runAll program [1] [1] [1 :: GF181]

  -- it "or 1" $ do
  --   let program = return $ true `Or` false
  --   runAll program [] [] [1 :: GF181]

  -- it "or 2" $ do
  --   let program = Or true <$> input Private
  --   runAll program [] [0] [1 :: GF181]
  --   runAll program [] [1] [1 :: GF181]

  -- it "xor 1" $ do
  --   let program = return $ true `Xor` false
  --   runAll program [] [] [1 :: GF181]

  -- it "xor 2" $ do
  --   let program = Xor <$> input Public <*> return true
  --   runAll program [0] [] [1 :: GF181]
  --   runAll program [1] [] [0 :: GF181]

  -- it "mixed 1" $ do
  --   let program = do
  --         x <- input Public
  --         y <- input Private
  --         let z = true
  --         return $ x `Or` y `And` z
  --   runAll program [0] [0] [0 :: GF181]
  --   runAll program [0] [1] [1 :: GF181]
  --   runAll program [1] [0] [1 :: GF181]
  --   runAll program [1] [1] [1 :: GF181]

  -- it "mixed 2" $ do
  --   let program = do
  --         x <- input Public
  --         y <- input Private
  --         let z = false
  --         w <- reuse $ x `Or` y
  --         return $ x `And` w `Or` z
  --   runAll program [0] [0] [0 :: GF181]
  --   runAll program [0] [1] [0 :: GF181]
  --   runAll program [1] [0] [1 :: GF181]
  --   runAll program [1] [1] [1 :: GF181]

  -- it "eq 1" $ do
  --   -- takes an input and see if its equal to False
  --   let program = do
  --         x <- input Public
  --         return $ x `eq` false

  --   runAll program [0] [] [1 :: GF181]
  --   runAll program [1] [] [0 :: GF181]

  -- it "conditional" $ do
  --   let program = do
  --         x <- inputField Public
  --         return $ cond (x `eq` 3) true false
  --   property $ \x -> do
  --     let expectedOutput = if x == 3 then [1] else [0]
  --     runAll program [x :: GF181] [] expectedOutput

  it "BtoF" $ do
    let program = do
          x <- input Public
          y <- input Private
          return $ BtoF x * BtoF y
    debug program
    runAll program [1 :: GF181] [1] [1]

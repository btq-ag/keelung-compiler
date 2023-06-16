{-# LANGUAGE DataKinds #-}

module Test.Interpreter.UInt.Addition (tests, run) where

import Keelung hiding (compile)
import Test.Hspec
import Test.Interpreter.Util
import Control.Monad

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "Addition / Subtraction" $ do

      it "2 variables" $ do
        let program = do
              x <- inputUInt @8 Public
              y <- inputUInt @8 Public
              return $ x + y
        runPrime (Prime 31) program [10, 30] [] [40]
        runPrime (Prime 5) program [10, 30] [] [40]

      it "3 variables" $ do
        let program = do
              x <- inputUInt @8 Public
              y <- inputUInt @8 Public
              z <- inputUInt @8 Public
              return $ x + y + z
        runPrime (Prime 31) program [10, 30, 5] [] [45]
        runPrime (Prime 5) program [10, 30, 5] [] [45]

      it "4 variables" $ do
        let program = do
              x <- inputUInt @8 Public
              y <- inputUInt @8 Public
              z <- inputUInt @8 Public
              w <- inputUInt @8 Public
              return $ x + y + z + w
        runPrime (Prime 31) program [10, 30, 5, 100] [] [145]
        runPrime (Prime 5) program [10, 30, 5, 100] [] [145]

      it "10 variables" $ do
        let program = do
              xs <- replicateM 10 (inputUInt @8 Public)
              return $ sum  xs
        let list = [10, 20, 30, 40, 50, 60, 70, 80, 90, 100]
        runPrime (Prime 31) program list [] [sum list `mod` 256]
        runPrime (Prime 5) program list [] [sum list `mod` 256]

      it "1 variable + constant" $ do
        let program = do
              x <- inputUInt @8 Public
              return $ x + 2
        runPrime (Prime 31) program [10] [] [12]
        runPrime (Prime 5) program [10] [] [12]

      it "2 variables + constant" $ do
        let program = do
              x <- inputUInt @8 Public
              y <- inputUInt @8 Public
              return $ x + y + 1
        runPrime (Prime 31) program [10, 30] [] [41]
        runPrime (Prime 5) program [10, 30] [] [41]

      it "3 variables + constant" $ do
        let program = do
              x <- inputUInt @8 Public
              y <- inputUInt @8 Public
              z <- inputUInt @8 Public
              return $ x + y + z + 1
        runPrime (Prime 31) program [10, 30, 40] [] [81]
        runPrime (Prime 5) program [10, 30, 40] [] [81]

      -- it "variables with subtraction" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         return $ - x
      --   runPrime (Prime 31) program [100] [] [156]
        -- debugPrime (Prime 7) program
        -- runPrime (Prime 7) program [100, 50] [] [50]
        -- runPrime (Prime 5) program [2, 1] [] [1]

      -- it "variables with subtraction" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         y <- inputUInt @8 Public
      --         return $ x - y
      --   -- runPrime (Prime 31) program [2, 1] [] [1]
      --   debugPrime (Prime 7) program
      --   runPrime (Prime 7) program [100, 50] [] [50]
        -- runPrime (Prime 5) program [2, 1] [] [1]

        -- let genPair = do
        --       x <- choose (0, 255)
        --       y <- choose (0, 255)
        --       z <- choose (0, 255)
        --       return (x, y, z)
        -- forAll genPair $ \(x, y, z) -> do
        --   let expected = [(x + y + z - z + 1) `mod` 256]
        --   runPrime (Prime 5) program [x,y] [] expected

      -- it "variables and constants with subtraction" $ do
      --   let program = do
      --         x <- inputUInt @32 Public
      --         y <- inputUInt @32 Public
      --         z <- inputUInt @32 Public
      --         return $ x + y - z + 4
      --   -- debugPrime (Prime 5) program

      --   let genPair = do
      --         x <- choose (0, 255)
      --         y <- choose (0, 255)
      --         z <- choose (0, 255)
      --         return (x, y, z)
      --   forAll genPair $ \(x, y, z) -> do
      --     let expected = [x + y - z + 4]
      --     runPrime (Prime 5) program [x, y, z] [] expected

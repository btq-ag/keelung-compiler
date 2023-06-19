{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

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
      it "variables (2 positive)" $ do
        let program = do
              x <- inputUInt @8 Public
              y <- inputUInt @8 Public
              return $ x + y
        runAll (Prime 997) program [10, 30] [] [40]
        -- runAll (Prime 31) program [10, 30] [] [40]
        -- runAll (Prime 5) program [10, 30] [] [40]

      -- it "3 variables" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         y <- inputUInt @8 Public
      --         z <- inputUInt @8 Public
      --         return $ x + y + z
      --   runAll (Prime 31) program [10, 30, 5] [] [45]
      --   runAll (Prime 5) program [10, 30, 5] [] [45]

      -- it "4 variables" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         y <- inputUInt @8 Public
      --         z <- inputUInt @8 Public
      --         w <- inputUInt @8 Public
      --         return $ x + y + z + w
      --   runAll (Prime 31) program [10, 30, 5, 100] [] [145]
      --   runAll (Prime 5) program [10, 30, 5, 100] [] [145]

      -- it "10 variables" $ do
      --   let program = do
      --         xs <- replicateM 10 (inputUInt @8 Public)
      --         return $ sum  xs
      --   let list = [10, 20, 30, 40, 50, 60, 70, 80, 90, 100]
      --   runAll (Prime 31) program list [] [sum list `mod` 256]
      --   runAll (Prime 5) program list [] [sum list `mod` 256]

      it "with constants (1 positive)" $ do
        let program = do
              x <- inputUInt @8 Public
              return $ x + 2
        runAll (Prime 997) program [10] [] [12]
        -- runAll (Prime 31) program [10] [] [12]
        -- runAll (Prime 5) program [10] [] [12]

      -- it "2 variables + constant" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         y <- inputUInt @8 Public
      --         return $ x + y + 1
      --   runAll (Prime 31) program [10, 30] [] [41]
      --   runAll (Prime 5) program [10, 30] [] [41]

      -- it "3 variables + constant" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         y <- inputUInt @8 Public
      --         z <- inputUInt @8 Public
      --         return $ x + y + z + 1
      --   runAll (Prime 31) program [10, 30, 40] [] [81]
      --   runAll (Prime 5) program [10, 30, 40] [] [81]

      it "variables (1 negative)" $ do
        let program = do
              x <- inputUInt @8 Public
              return $ - x
        -- let field = 997
        debug (Prime 997) program
        runAll (Prime 997) program [100] [] [156]

      -- it "variables with subtraction" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         return $ - x - x
      --   let field = 13
      --   -- debug (Prime field) program
      --   runAll (Prime field) program [100] [] [56]
        -- debugPrime (Prime 7) program
        -- runAll (Prime 7) program [100, 50] [] [50]
        -- runAll (Prime 5) program [2, 1] [] [1]

      -- it "variables with subtraction" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         y <- inputUInt @8 Public
      --         return $ x - y
      --   -- runAll (Prime 31) program [2, 1] [] [1]
      --   debugPrime (Prime 7) program
      --   runAll (Prime 7) program [100, 50] [] [50]
        -- runAll (Prime 5) program [2, 1] [] [1]

        -- let genPair = do
        --       x <- choose (0, 255)
        --       y <- choose (0, 255)
        --       z <- choose (0, 255)
        --       return (x, y, z)
        -- forAll genPair $ \(x, y, z) -> do
        --   let expected = [(x + y + z - z + 1) `mod` 256]
        --   runAll (Prime 5) program [x,y] [] expected

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
      --     runAll (Prime 5) program [x, y, z] [] expected

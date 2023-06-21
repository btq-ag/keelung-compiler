{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Interpreter.UInt.Addition (tests, run) where

import Keelung hiding (compile)
import Test.Hspec
import Test.Interpreter.Util
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "Addition / Subtraction" $ do

      it "2 positive variables" $ do
        let program = do
              x <- inputUInt @2 Public
              y <- inputUInt @2 Public
              return $ x + y
        let genPair = do
              x <- choose (0, 3)
              y <- choose (0, 3)
              return (x, y)
        forAll genPair $ \(x, y) -> do
          let expected = [(x + y) `mod` 4]
          runAll (Prime 5) program [x, y] [] expected
          runAll (Prime 7) program [x, y] [] expected
          runAll (Prime 11) program [x, y] [] expected
          runAll (Prime 13) program [x, y] [] expected
          runAll (Prime 17) program [x, y] [] expected
          runAll (Prime 19) program [x, y] [] expected

      -- it "2 positive variables" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         y <- inputUInt @8 Public
      --         return $ x + y
      --   let genPair = do
      --         x <- choose (0, 255)
      --         y <- choose (0, 255)
      --         return (x, y)
      --   forAll genPair $ \(x, y) -> do
      --     let expected = [(x + y) `mod` 256]
      --     runAll (Prime 7) program [x, y] [] expected

        -- runAll (Prime 997) program [5] [] [30]
        -- runAll (Prime 37) program [5] [] [30]
        -- debug (Prime 5) program
        -- runAll (Prime 5) program [2] [] [6]

      -- it "4 positive variables" $ do
      --   let program = do
      --         x <- inputUInt @4 Public
      --         return $ x + x + x + x
      --   -- runAll (Prime 997) program [5] [] [30]
      --   -- runAll (Prime 37) program [5] [] [30]
      --   debug (Prime 5) program
      --   runAll (Prime 5) program [2] [] [8]

      -- it "5 positive variables" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         return $ x + x + x + x + x
      --   -- runAll (Prime 997) program [5] [] [30]
      --   -- runAll (Prime 37) program [5] [] [30]
      --   runAll (Prime 5) program [5] [] [25]

      -- it "6 positive variables" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         return $ x + x + x + x + x + x
      --   -- runAll (Prime 997) program [5] [] [30]
      --   -- runAll (Prime 37) program [5] [] [30]
      --   runAll (Prime 5) program [5] [] [30]

      -- it "7 positive variables" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         return $ x + x + x + x + x + x + x
      --   -- runAll (Prime 997) program [5] [] [30]
      --   -- runAll (Prime 37) program [5] [] [30]
      --   runAll (Prime 5) program [5] [] [35]

      -- it "8 positive variables" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         return $ x + x + x + x + x + x + x + x
      --   -- runAll (Prime 997) program [5] [] [30]
      --   -- runAll (Prime 37) program [5] [] [30]
      --   runAll (Prime 5) program [5] [] [40]

      -- it "9 positive variables" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         return $ x + x + x + x + x + x + x + x + x
      --   -- runAll (Prime 997) program [5] [] [30]
      --   -- runAll (Prime 37) program [5] [] [30]
      --   runAll (Prime 5) program [5] [] [45]

      -- it "2 positive variables" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         y <- inputUInt @8 Public
      --         return $ x + y
      --   runAll (Prime 997) program [10, 30] [] [40]
      --   runAll (Prime 37) program [10, 30] [] [40]
      --   -- runAll (Prime 5) program [10, 30] [] [40]

      -- it "1 positive variable / constant" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         return $ x + 2
      --   runAll (Prime 997) program [10] [] [12]
      --   runAll (Prime 37) program [10] [] [12]
      --   -- runAll (Prime 5) program [10] [] [12]

      -- it "1 negative variable" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         return $ - x
      --   runAll (Prime 997) program [100] [] [156]
      --   runAll (Prime 37) program [100] [] [156]
      --   -- runAll (Prime 5) program [100] [] [156]

      -- it "1 negative variable / constant" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         return $ 10 - x
      --   runAll (Prime 997) program [100] [] [166]
      --   runAll (Prime 37) program [100] [] [166]

      -- it "2 negative variables / constant" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         y <- inputUInt @8 Public
      --         return $ 10 - x - y
      --   runAll (Prime 997) program [100, 20] [] [146]
      --   runAll (Prime 37) program [100, 20] [] [146]

      -- it "2 positive variables / 2 negative variables / constant" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         y <- inputUInt @8 Public
      --         return $ 10 + x - y
      --   runAll (Prime 997) program [100, 20] [] [90]
      --   runAll (Prime 37) program [100, 20] [] [90]

      -- it "3 positive variables" $ do
      --   let program = do
      --         x <- inputUInt @8 Public
      --         y <- inputUInt @8 Public
      --         z <- inputUInt @8 Public
      --         return $ x + y + z
        
      --   -- runAll (Prime 31) program [10, 30, 5] [] [45]
      --   -- runAll (Prime 5) program [10, 30, 5] [] [45]
      --   runAll (Prime 7) program [100, 20, 10] [] [130]

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

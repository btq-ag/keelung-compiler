{-# LANGUAGE DataKinds #-}

-- {-# LANGUAGE TypeApplications #-}

module Test.Interpreter.UInt.DivMod (tests, run) where

import Keelung hiding (compile)
import Keelung.Compiler.Compile.Error qualified as Compiler
import Keelung.Compiler.Error (Error (..))
import Keelung.Interpreter qualified as Interpreter
import Test.Hspec
import Test.Interpreter.Util
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "DivMod" $ do
    it "performDivMod (quotient & remainder unknown)" $ do
      let program = do
            dividend <- input Public :: Comp (UInt 5)
            divisor <- input Public
            performDivMod dividend divisor

    --   -- debug (Prime 263) program
      -- debugUnoptimized gf181 program
      printLogUnoptimized gf181 program [7, 3] []
      -- runAll gf181 program [7, 3] [] [2, 1]
      -- runAll (Prime 31) program [30, 4] [] [7, 2]
    --   -- debug (Prime 31) program
    --   -- printLog (Prime 17) program [13, 3] []
    --   -- printLog (Prime 257) program [64, 3] []
    --   -- printLog (Prime 263) program [20, 7] []
    --   -- runAll (Prime 23) program [20, 7] [] [2, 6]
    --   -- runAll (Prime 263) program [20, 7] [] [2, 6]
    --   -- runAll (Prime 263) program [20, 7] [] [2, 6]
    --   let genPair = do
    --         dividend <- choose (0, 255)
    --         divisor <- choose (1, 255)
    --         return (dividend, divisor)

    --   forAll genPair $ \(dividend, divisor) -> do
    --     let expected = [dividend `div` divisor, dividend `mod` divisor]
    --     -- runAll (Prime 1031) program [dividend, divisor] [] expected
    --     -- runAll (Prime 257) program [dividend, divisor] [] expected
    --     runAll (Prime 251) program [dividend, divisor] [] expected

    -- it "performDivMod (on constants) (issue #18)" $ do
    --   -- 7 = 3 * 2 + 1
    --   let program = performDivMod 7 (3 :: UInt 4)
    --   -- runAll (Prime 251) program [] [] [2, 1]
    --   debug (Prime 251) program

--     it "assertDivMod (on constants) (issue #18)" $ do
--       let program = assertDivMod 7 (3 :: UInt 4) 2 1
--       runAll gf181 program [] [] []

--     it "assertDivMod (with wrong quotient constant)" $ do
--       let program = assertDivMod 7 (3 :: UInt 4) 3 1
--       throwBoth
--         gf181
--         program
--         []
--         []
--         (InterpreterError (Interpreter.DivModQuotientError 7 3 2 3))
--         (CompilerError (Compiler.ConflictingValuesB True False) :: Error GF181)

--     it "assertDivMod (with wrong remainder constant)" $ do
--       let program = assertDivMod 7 (3 :: UInt 4) 2 0
--       throwBoth
--         gf181
--         program
--         []
--         []
--         (InterpreterError (Interpreter.DivModRemainderError 7 3 1 0))
--         (CompilerError (Compiler.ConflictingValuesB False True) :: Error GF181)

--     it "assertDivMod (multiple statements)" $ do
--       let program = do
--             a <- input Public :: Comp (UInt 5)
--             b <- input Public
--             c <- input Private
--             d <- input Public
--             (q0, r0) <- performDivMod a b
--             (q1, r1) <- performDivMod c d
--             return [q0, r0, q1, r1]
--       runAll gf181 program [20, 7, 8] [21] [2, 6, 2, 5]

--     it "assertDivMod (multiple statements chained together)" $ do
--       let program = do
--             a <- input Public :: Comp (UInt 5)
--             b <- input Public
--             (q0, r0) <- performDivMod a b
--             (q1, r1) <- performDivMod q0 b
--             return [q0, r0, q1, r1]
--       runAll gf181 program [25, 3] [] [8, 1, 2, 2]

--     it "performDivMod (before assertions)" $ do
--       let program = do
--             a <- input Public :: Comp (UInt 5)
--             b <- input Public
--             (q, r) <- performDivMod a b
--             assert $ q `eq` r
--       runAll gf181 program [10, 4] [] []

--     it "performDivMod (before reuse)" $ do
--       let program = do
--             a <- input Public :: Comp (UInt 5)
--             b <- input Public
--             (q, _) <- performDivMod a b
--             reuse q
--       runAll gf181 program [10, 4] [] [2]

--     it "performDivMod (after reuse)" $ do
--       let program = do
--             a <- reuse =<< input Public :: Comp (UInt 5)
--             b <- input Public
--             (q, r) <- performDivMod a b
--             assert $ q `eq` r
--       runAll gf181 program [10, 4] [] []

--     it "assertDivMod (dividend unknown)" $ do
--       let program = do
--             dividend <- freshVarUInt
--             divisor <- input Public :: Comp (UInt 6)
--             quotient <- input Public
--             remainder <- input Private
--             assertDivMod dividend divisor quotient remainder
--             return dividend
--       runAll gf181 program [7, 2] [6] [20]

--     it "assertDivMod (divisor & remainder unknown)" $ do
--       let program = do
--             dividend <- input Public :: Comp (UInt 4)
--             divisor <- freshVarUInt
--             quotient <- input Public
--             remainder <- freshVarUInt
--             assertDivMod dividend divisor quotient remainder
--             return (divisor, remainder)
--       runAll gf181 program [7, 2] [] [3, 1]

--     it "assertDivMod (quotient & remainder unknown)" $ do
--       let program = do
--             dividend <- input Public :: Comp (UInt 6)
--             divisor <- input Public
--             quotient <- freshVarUInt
--             remainder <- freshVarUInt
--             assertDivMod dividend divisor quotient remainder
--             return (quotient, remainder)
--       runAll gf181 program [34, 6] [] [5, 4]

-- --   describe "Div / Mod" $ do
-- --     it "Constants only" $ do
-- --       let program x y = do
-- --             return $ x * (y :: UInt 6)
-- --       let genPair = do
-- --             x <- choose (-63, 63)
-- --             y <- choose (-63, 63)
-- --             return (x, y)
-- --       forAll genPair $ \(x, y) -> do
-- --         let expected = [(x * y) `mod` 64]
-- --         runAll (Prime 5) (program (fromInteger x) (fromInteger y)) [] [] expected
-- --         runAll (Prime 257) (program (fromInteger x) (fromInteger y)) [] [] expected

-- --     it "1-limb x 1-limb" $ do
-- --       let program = do
-- --             x <- inputUInt @4 Public
-- --             y <- inputUInt @4 Public
-- --             return $ x * y
-- --       -- debug (Prime 1031) program
-- --       let genPair = do
-- --             x <- choose (-15, 15)
-- --             y <- choose (-15, 15)
-- --             return (x, y)

-- --       forAll genPair $ \(x, y) -> do
-- --         let expected = [(x * y) `mod` 16]
-- --         runAll (Prime 1031) program [x, y] [] expected

-- --     it "1-limb variable x 1-limb constant" $ do
-- --       let program y = do
-- --             x <- inputUInt @4 Public
-- --             return $ x * fromInteger y
-- --       let genPair = do
-- --             x <- choose (-15, 15)
-- --             y <- choose (-15, 15)
-- --             return (x, y)
-- --       forAll genPair $ \(x, y) -> do
-- --         let expected = [(x * y) `mod` 16]
-- --         runAll (Prime 1031) (program y) [x] [] expected
-- --     --   runAll (Prime 17) (program y) [x] [] expected

-- --     it "2-limb x 2-limb" $ do
-- --       let program = do
-- --             x <- inputUInt @4 Public
-- --             y <- inputUInt @4 Public
-- --             return $ x * y
-- --       -- debug (Prime 17) program
-- --       -- runAll (Prime 17) program [10, 2] [] [4]
-- --       let genPair = do
-- --             x <- choose (-15, 15)
-- --             y <- choose (-15, 15)
-- --             return (x, y)
-- --       forAll genPair $ \(x, y) -> do
-- --         let expected = [(x * y) `mod` 16]
-- --         runAll (Prime 17) program [x, y] [] expected

-- --     it "2-limb variable x 2-limb constant" $ do
-- --       let program y = do
-- --             x <- inputUInt @4 Public
-- --             return $ x * fromInteger y
-- --       -- runAll (Prime 17) (program 0) [10] [] [0]
-- --       let genPair = do
-- --             x <- choose (-15, 15)
-- --             y <- choose (-15, 15)
-- --             return (x, y)
-- --       forAll genPair $ \(x, y) -> do
-- --         let expected = [(x * y) `mod` 16]
-- --         runAll (Prime 1031) (program y) [x] [] expected
-- --         runAll (Prime 17) (program y) [x] [] expected

-- --     it "3-limb x 3-limb" $ do
-- --       let program = do
-- --             x <- inputUInt @6 Public
-- --             y <- inputUInt @6 Public
-- --             return $ x * y
-- --       -- debug (Prime 17) program
-- --       -- runAll (Prime 17) program [10, 2] [] [4]
-- --       let genPair = do
-- --             x <- choose (-63, 63)
-- --             y <- choose (-63, 63)
-- --             return (x, y)
-- --       forAll genPair $ \(x, y) -> do
-- --         let expected = [(x * y) `mod` 64]
-- --         runAll (Prime 17) program [x, y] [] expected

-- --     it "3-limb variable x 3-limb constant" $ do
-- --       let program y = do
-- --             x <- inputUInt @6 Public
-- --             return $ x * fromInteger y
-- --       let genPair = do
-- --             x <- choose (-63, 63)
-- --             y <- choose (-63, 63)
-- --             return (x, y)
-- --       forAll genPair $ \(x, y) -> do
-- --         let expected = [(x * y) `mod` 64]
-- --         runAll (Prime 17) (program y) [x] [] expected

-- -- --     it "Byte / GF(1031)" $ do

-- -- --       let program y = do
-- -- --             x <- inputUInt @32 Public
-- -- --             return $ x * fromInteger y
-- -- --       debug (Prime 1031) (program 1)
-- --       -- let genPair = do
-- --       --       x <- (arbitrary :: Gen Int)
-- --       --       y <- (arbitrary :: Gen Int)
-- --       --       return (toInteger x, toInteger y)
-- --       -- forAll genPair $ \(x, y) -> do
-- --       --   let expected = [(x * y) `mod` (2 ^ 32)]
-- --       --   runAll (Prime 17) (program y) [x] [] expected

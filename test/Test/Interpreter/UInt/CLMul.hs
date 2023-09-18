{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Interpreter.UInt.CLMul (tests, run) where

import Data.Word
import Keelung hiding (compile)
import Test.Hspec
import Test.Interpreter.Util
import Test.QuickCheck hiding ((.&.))
import qualified Keelung.Interpreter.Arithmetics as U

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "Carry-less Multiplication" $ do
    it "Constants only" $ do
      let program x y = do
            return $ x .*. (y :: UInt 6)
      let genPair = do
            x <- choose (-63, 63)
            y <- choose (-63, 63)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [U.uintValue (U.integerCLMulU (U.new 6 x) (U.new 6 y))]
        runAll (Prime 5) (program (fromInteger x) (fromInteger y)) [] [] expected
        runAll (Prime 257) (program (fromInteger x) (fromInteger y)) [] [] expected

--     it "2 byte variables" $ do
--       let program = do
--             x <- inputUInt @8 Public
--             y <- inputUInt @8 Public
--             return $ x * y
--       forAll arbitrary $ \(x :: Word8, y :: Word8) -> do
--         let expected = [toInteger (x * y)]
--         runAll (Prime 17) program [toInteger x, toInteger y] [] expected
--         runAll (Prime 257) program [toInteger x, toInteger y] [] expected
--         runAll (Prime 1031) program [toInteger x, toInteger y] [] expected

--     it "2 Word64 variables" $ do
--       let program = do
--             x <- inputUInt @64 Public
--             y <- inputUInt @64 Public
--             return $ x * y
--       forAll arbitrary $ \(x :: Word64, y :: Word64) -> do
--         let expected = [toInteger (x * y)]
--         --   runAll (Prime 17) program [toInteger x, toInteger y] [] expected
--         --   runAll (Prime 1031) program [toInteger x, toInteger y] [] expected
--         runAll gf181 program [toInteger x, toInteger y] [] expected

--     it "1 variable / 1 constant" $ do
--       let program y = do
--             x <- inputUInt @8 Public
--             return $ x * fromInteger y
--       -- debug (Prime 17) (program 32)
--       -- debug (Prime 1031) (program 32)
--       -- runAll (Prime 17) (program 16) [3] [] [48]
--       -- runAll (Prime 17) (program 32) [29] [] [160]
--       -- runAll (Prime 257) (program 32) [29] [] [160]
--       -- runAll (Prime 1031) (program 32) [29] [] [160]
--       -- runAll (Prime 17) (program 26) [25] [] [138]
--       -- runAll (Prime 257) (program 26) [25] [] [138]
--       -- runAll (Prime 1031) (program 26) [25] [] [138]

--       let genPair = do
--             x <- (arbitrary :: Gen Word8)
--             y <- (arbitrary :: Gen Word8)
--             return (toInteger x, toInteger y)
--       forAll genPair $ \(x, y) -> do
--         let expected = [(x * y) `mod` 256]
--         runAll (Prime 17) (program y) [x] [] expected
--         runAll (Prime 257) (program y) [x] [] expected
--         runAll (Prime 1031) (program y) [x] [] expected

--     it "with addition" $ do
--       let program = do
--             x <- inputUInt @8 Public
--             y <- inputUInt @8 Public
--             z <- inputUInt @8 Public
--             return $ x * y + z
--       let genPair = do
--             x <- (arbitrary :: Gen Word8)
--             y <- (arbitrary :: Gen Word8)
--             z <- (arbitrary :: Gen Word8)
--             return (toInteger x, toInteger y, toInteger z)
--       forAll genPair $ \(x, y, z) -> do
--         let expected = [(x * y + z) `mod` 256]
--         runAll (Prime 17) program [x, y, z] [] expected
--         runAll (Prime 257) program [x, y, z] [] expected
--         runAll (Prime 1031) program [x, y, z] [] expected

--     it "with subtraction" $ do
--       let program = do
--             x <- inputUInt @8 Public
--             y <- inputUInt @8 Public
--             z <- inputUInt @8 Public
--             return $ -x * y - z
--       let genPair = do
--             x <- (arbitrary :: Gen Word8)
--             y <- (arbitrary :: Gen Word8)
--             z <- (arbitrary :: Gen Word8)
--             return (toInteger x, toInteger y, toInteger z)
--       forAll genPair $ \(x, y, z) -> do
--         let expected = [(-x * y - z) `mod` 256]
--         runAll (Prime 17) program [x, y, z] [] expected
--         runAll (Prime 257) program [x, y, z] [] expected
--         runAll (Prime 1031) program [x, y, z] [] expected

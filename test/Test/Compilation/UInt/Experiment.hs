{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Experiment (tests, run) where

import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck
import qualified Keelung.Data.U as U
import Test.HUnit
import Control.Monad

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Binary field" $ do
    -- it "2 positive variables / Byte" $ do
    --   let program = do
    --         x <- inputUInt @8 Public
    --         y <- inputUInt @8 Public
    --         return $ x * y
    --   property $ \(x, y :: Word8) -> do
    --     let expected = map toInteger [x * y]
    --     runAll (Binary 7) program (map toInteger [x, y]) [] expected

    -- it "2 positive variables / Word64" $ do
    --   let program = do
    --         x <- inputUInt @64 Public
    --         y <- inputUInt @64 Public
    --         return $ x * y
    --   property $ \(x, y :: Word64) -> do
    --     let expected = map toInteger [x * y]
    --     runAll (Binary 7) program (map toInteger [x, y]) [] expected

    -- it "modInv N (mod 71)" $ do
    --   let prime = 71
    --   let program = do
    --         x <- input Public :: Comp (UInt 8)
    --         return $ modInv x prime
    --   let expected = [fromInteger 22]
    --   forM_ [Prime 17] $ \field -> do
    --     runAll field program [42] [] expected

    it "modInv N (mod 7)" $ do

      -- 
      -- 6 * 6 = 7 * 5 + 1 (mod 7)
      let prime = 7
      let program = do
            x <- input Public :: Comp (UInt 4)
            return $ modInv x prime
      debug (Prime 17) program
      -- runAll (Prime 17) program [6] [] [6]
      -- runAll (Prime 17) program [2] [] [4]

      -- printLog (Prime 17) program [6] []


      -- let expected = [fromInteger 6]
      -- forM_ [Prime 17] $ \field -> do
      --   runAll field program [6] [] expected

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Compilation.Experiment (run, tests) where

import Control.Monad (forM_)
import Data.Either qualified as Either
import Data.Word (Word8)
import Keelung hiding (MulU, VarUI)
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Test.Arbitrary (arbitraryUOfWidth)
import Test.Hspec
import Test.QuickCheck
import Test.Util

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Experiment" $ do
  it "failure" $ do
    let program divisor = do
          dividend <- input Public :: Comp (UInt 8)
          performDivMod dividend divisor
    let (dividend, divisor) = (12, 1) :: (Word8, Word8)
    let expected = map fromIntegral [dividend `div` divisor, dividend `mod` divisor]
    -- debug gf181 (program (fromIntegral divisor))
    --     forM_ [gf181, Prime 17, Binary 7] $ \field -> do
    check gf181 (program (fromIntegral divisor)) [fromIntegral dividend] [] expected
    check (Prime 17) (program (fromIntegral divisor)) [fromIntegral dividend] [] expected
    check (Binary 7) (program (fromIntegral divisor)) [fromIntegral dividend] [] expected

--   it "variable dividend / constant divisor = 1" $ do
--     let program divisor = do
--           dividend <- input Public :: Comp (UInt 8)
--           performDivMod dividend divisor
--     let genPair = do
--           dividend <- chooseInt (0, 255)
--           return (dividend, 1)

--     forAll genPair $ \(dividend, divisor) -> do
--       let expected = map fromIntegral [dividend `div` divisor, dividend `mod` divisor]
--       --     debug gf181 (program (fromIntegral divisor))
--       --     forM_ [gf181, Prime 17, Binary 7] $ \field -> do
--       --     check gf181 (program (fromIntegral divisor)) [fromIntegral dividend] [] expected
--       --     check (Prime 17) (program (fromIntegral divisor)) [fromIntegral dividend] [] expected
--       check (Binary 7) (program (fromIntegral divisor)) [fromIntegral dividend] [] expected

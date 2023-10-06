{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Compilation.UInt.Misc (tests, run) where

import Keelung hiding (compile)
import Keelung.Data.U qualified as U
import Test.Compilation.Util
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "Carry-less Multiplication" $ do
    it "1 variable / 1 constant" $ do
      let program y = do
            x <- inputUInt @8 Public
            return $ x .*. fromInteger y
      let x = 1
      let y = 2
      let expected = [U.uValue (U.clMul (U.new 8 (toInteger x)) (U.new 8 (toInteger y)))]
      runAll (Prime 17) (program y) [x] [] expected
      runAll (Prime 257) (program y) [x] [] expected
      runAll (Prime 1031) (program y) [x] [] expected
      -- debug (Prime 257) (program y)
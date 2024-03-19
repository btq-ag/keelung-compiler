{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment (run, tests) where

import Keelung
import Keelung.Data.U qualified as U
import Test.Arbitrary ()
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "Join" $ do
    it "constant (slice width: 4 / 4)" $ do
      let genParam = do
            x <- chooseInteger (0, 15)
            y <- chooseInteger (0, 15)
            return (x, y)

      let program x y = do
            let u = fromInteger x :: UInt 4
            let v = fromInteger y :: UInt 4
            return $ u `join` v :: Comp (UInt 8)

      forAll genParam $ \(x, y) -> do
        let expected = [toInteger (U.join (U.new 4 x) (U.new 4 y))]
        testCompiler (Binary 7) (program x y) [] [] expected
        testCompiler (Prime 17) (program x y) [] [] expected
        testCompiler gf181 (program x y) [] [] expected
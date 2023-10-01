{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.CLDivMod (tests, run) where

-- import Data.Word
import Keelung
-- import Keelung.Data.U qualified as U

import Keelung.Data.U qualified as U
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

clDiv :: Width -> Integer -> Integer -> Integer
clDiv width x y = U.uValue (U.new width x `U.clDiv` U.new width y)

clMod :: Width -> Integer -> Integer -> Integer
clMod width x y = U.uValue (U.new width x `U.clMod` U.new width y)

tests :: SpecWith ()
tests =
  describe "Carry-less Div/Mod" $ do
    it "performDivMod (quotient & remainder unknown)" $ do
      let width = 8
      let program = do
            dividend <- input Public :: Comp (UInt 8)
            divisor <- input Public
            performCLDivMod dividend divisor

      let genPair = do
            dividend <- choose (0, 255)
            divisor <- choose (1, 255)
            return (dividend, divisor)

      forAll genPair $ \(dividend, divisor) -> do
        let expected = [clDiv width dividend divisor, clMod width dividend divisor]
        runAll gf181 program [dividend, divisor] [] expected
        runAll (Prime 17) program [dividend, divisor] [] expected
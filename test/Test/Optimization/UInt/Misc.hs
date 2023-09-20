{-# LANGUAGE DataKinds #-}

module Test.Optimization.UInt.Misc (tests, run) where

import Keelung
import Test.Hspec
import qualified Data.Bits
-- import Test.Optimization.Util
-- import Keelung.Compiler.Linker
import Test.QuickCheck
import Test.Interpreter.Util
-- 
run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Misc" $ do
  -- describe "Carry-less Multiplication" $ do
  --   it "2 byte variables" $ do
  --     -- constraint breakdown:
  --     -- I/O: 24 = 2 * 8 + 8
  --     -- ANDs: 36 = 8 * 9 / 2
  --     -- XORs: 7
  --     (cs, cs') <- executeGF181 $ do
  --       x <- input Public :: Comp (UInt 8)
  --       y <- input Public :: Comp (UInt 8)
  --       return (x .*. y)
  --     -- print $ linkConstraintModule cs'
  --     cs `shouldHaveSize` 75
  --     cs' `shouldHaveSize` 67


  describe "exclusive disjunction" $ do
    it "2 variables / byte" $ do
      let program = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            return $ x .^. y
      forAll
        ( do
            x <- choose (0, 255)
            y <- choose (0, 255)
            return (x, y)
        )
        $ \(x, y) -> do
          let expected = [Data.Bits.xor x y]
          runAll (Prime 13) program [x, y] [] expected
-- --  (250,75,13)

    it "variables with constants / byte / Prime 13" $ do
      let program = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            z <- inputUInt @8 Public
            return $ x .^. y .^. z .^. 3
      forAll
        ( do
            x <- choose (0, 255)
            y <- choose (0, 255)
            z <- choose (0, 255)
            return (x, y, z)
        )
        $ \(x, y, z) -> do
          let expected = [x `Data.Bits.xor` y `Data.Bits.xor` z `Data.Bits.xor` 3]
          runAll (Prime 13) program [x, y, z] [] expected

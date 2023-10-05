{-# LANGUAGE DataKinds #-}

-- {-# LANGUAGE TypeApplications #-}

module Test.Optimization.UInt.Misc (tests, run) where

import Keelung
-- import Keelung.Compiler.Linker
import Test.Hspec
import Test.Optimization.Util

-- --
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
  --     (_cs, cs') <- executeGF181 $ do
  --       x <- input Public :: Comp (UInt 8)
  --       y <- input Public :: Comp (UInt 8)
  --       return (x .*. y)
  --     -- print cs'
  --     -- print $ linkConstraintModule cs'

  --     _cs `shouldHaveSize` 91
  --     cs' `shouldHaveSize` 87

  describe "Carry-less Multiplication" $ do
    it "2 2-bit variables" $ do
      -- constraint breakdown:
      -- I/O: 24 = 2 * 8 + 8
      -- ANDs: 36 = 8 * 9 / 2
      -- XORs: 7
      (_cs, cs') <- executeGF181 $ do
        x <- input Public :: Comp (UInt 2)
        y <- input Public :: Comp (UInt 2)
        performCLDivMod x y
      -- print _cs
      -- print cs'
      -- print $ linkConstraintModule cs'
      _cs `shouldHaveSize` 33
      cs' `shouldHaveSize` 20
-- it "1 variable / 1 constant" $ do
--   -- constraint breakdown:
--   -- I/O: 24 = 2 * 8 + 8
--   -- ANDs: 36 = 8 * 9 / 2
--   -- XORs: 7
--   (cs, cs') <- executeGF181 $ do
--     x <- input Public :: Comp (UInt 8)
--     return (x .*. 1)
--   -- print cs
--   -- print $ linkConstraintModule cs'
--   cs `shouldHaveSize` 76
--   cs' `shouldHaveSize` 68

--   describe "exclusive disjunction" $ do
--     it "2 variables / byte" $ do
--       let program = do
--             x <- inputUInt @8 Public
--             y <- inputUInt @8 Public
--             return $ x .^. y
--       forAll
--         ( do
--             x <- choose (0, 255)
--             y <- choose (0, 255)
--             return (x, y)
--         )
--         $ \(x, y) -> do
--           let expected = [Data.Bits.xor x y]
--           runAll (Prime 13) program [x, y] [] expected
-- -- --  (250,75,13)

-- it "xor" $ do
--   let program = do
--         x <- inputBool Public
--         y <- inputBool Public
--         z <- inputBool Public
--         return $ x .^. y .^. z
--   -- forAll
--   --   ( do
--   --       x <- choose (0, 255)
--   --       y <- choose (0, 255)
--   --       z <- choose (0, 255)
--   --       return (x, y, z)
--   --   )
--   --   $ \(x, y, z) -> do
--   --     let expected = [x `Data.Bits.xor` y `Data.Bits.xor` z `Data.Bits.xor` 3]
--   --     runAll (Prime 13) program [x, y, z] [] expected
--   debug gf181 program

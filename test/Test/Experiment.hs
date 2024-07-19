{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Test.Experiment (run, tests) where

import Control.Monad (forM_)
import Data.Bits qualified
import Data.Field.Galois
import Data.IntMap qualified as IntMap
import Keelung hiding (MulU, VarUI)
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.Relations qualified as Relations
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.Reference
import Keelung.Solver.BinRep qualified as BinRep
import Test.Hspec
import Test.QuickCheck
import Test.Util

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Experiment" $ do
-- debugSolver (Prime 5) program [fromIntegral (x `mod` 4)] []
-- check (Binary 7) program [fromIntegral (x `mod` 4)] [] [fromIntegral expected]
-- it "variable dividend / constant divisor" $ do
--     let program divisor = do
--           dividend <- input Public :: Comp (UInt 8)
--           performDivMod dividend divisor
--     let (dividend, divisor) = (44, 2)
--     let _expected = [dividend `div` divisor, dividend `mod` divisor]
--     -- check gf181 (program (fromIntegral divisor)) [dividend] [] expected
--     -- check (Prime 17) (program (fromIntegral divisor)) [dividend] [] expected
--     check (Binary 7) (program (fromIntegral divisor)) [dividend] [] _expected
--     -- debugSolver (Binary 7) (program (fromIntegral divisor)) [dividend] []

-- it "Homemade div/mod" $ do
--   let program = do
--         dividend <- input Public :: Comp (UInt 8)
--         divisor <- input Public :: Comp (UInt 8)
--         let p = dividend `mul` divisor
--         remainder <- freshVarUInt :: Comp (UInt 16)
--         quotient <- freshVarUInt :: Comp (UInt 16)
--         -- dividend = divisor * quotient + remainder
--         assert $ (dividend `join` 0) `eq` (p + remainder)
--         -- 0 ≤ remainder < divisor
--         assertGT divisor 0
--         assert $ remainder `lt` (divisor `join` 0)

--         solve dividend $ \dividendVal -> do
--           assertHint $ dividendVal

--         return $ slice quotient (0, 8) :: Comp (UInt 8)

-- debug gf181 program

-- check gf181 program [10, 3] [] [3]

  describe "from (UInt 1) variable" $ do
    let program = do
          x <- input Public -- $1
          h <- (freshVarUInt :: Comp (UInt 8)) >>= toField -- $5 - $12 and $2
          m <- (freshVarUInt :: Comp (UInt 1)) >>= toField -- $4 and $3
          -- assert $ 1 `eq` (x + m)
          assert $ 1 `eq` (x + m + h)
          return x -- $0
    it "GF181" $ do
      -- check gf181 program [n] [] [(n + 1) `mod` 2]
      -- debugO0 gf181 program
      debug gf181 program

    -- it "Prime 2" $ do
    --   forAll (chooseInteger (-10, 4)) $ \n -> do
    --     check (Prime 2) program [n] [] [n `mod` 2]
    -- it "Binary 7" $ do
    --   forAll (chooseInteger (-10, 8)) $ \n -> do
    --     check (Binary 7) program [n] [] [n `mod` 2]
    
  -- it "PK inverse" $ do
  --   testInversePK 0x00 0x00

testInversePK :: Integer -> Integer -> IO ()
testInversePK inputs _expected = do
  -- testSolver pkField (input Public >>= inversePK) [inputs] [] [_expected]
  debugSolver pkField (input Public >>= inversePK) [inputs] []
  debug pkField (input Public >>= inversePK)

pkField :: FieldType
pkField = Binary 340282366920938463463374607431768211457

-- | Inverse of a field element in PK
--   Given a field element `x`, find `out` such that `x * out = 1`
inversePK :: Field -> Comp Field
inversePK x = do -- $1
  out <- freshVarField -- $0
  h <- (freshVarUInt :: Comp (UInt 8)) >>= toField -- $6 - $13 and $2
  m <- (freshVarUInt :: Comp (UInt 1)) >>= toField -- $5 and $3
  assert $ 1 `eq` (x * out + 283 * h + m)
  assert $ 0 `eq` ((out + 256 * x + 65536 * h + 16777216 * (1 + m)) * m)
  return out

-- Right R1CS {
--   Constriant (14): 
--     Ordinary constraints (5):

--       1 + 283$2 + $3 + $4 = 0
--       $2 + $6 + 2$7 + 4$8 + 8$9 + 16$10 + 32$11 + 64$12 + 128$13 = 0
--       $3 + $5 = 0
--       $1 * $0 = $4
--       (16777216 + $0 + 256$1 + 65536$2 + 16777216$3) * $3 = 0

--     Boolean constraints (9):

--       $5 = $5 * $5
--         ...
--       $13 = $13 * $13

--   Variables (14):

--     Output variable:        $0
--     Public input variable:  $1
--     Other variables:        $2 ... $13

-- }
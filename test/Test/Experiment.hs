{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Test.Experiment (run, tests) where

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


  it "variable dividend / constant divisor" $ do
      let program divisor = do
            dividend <- input Public :: Comp (UInt 8)
            performDivMod dividend divisor
      let (dividend, divisor) = (44, 2)
      let expected = [dividend `div` divisor, dividend `mod` divisor]
      -- check gf181 (program (fromIntegral divisor)) [dividend] [] expected
      -- check (Prime 17) (program (fromIntegral divisor)) [dividend] [] expected
      -- check (Binary 7) (program (fromIntegral divisor)) [dividend] [] expected
      debugSolver (Binary 7) (program (fromIntegral divisor)) [dividend] []


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
  -- it "PK inverse" $ do
  --   testInversePK 0x00 0x00

testInversePK :: Integer -> Integer -> IO ()
testInversePK inputs expected = do
  -- testSolver pkField (input Public >>= inversePK) [inputs] [] [expected]
  debugSolver pkField (input Public >>= inversePK) [inputs] []

pkField :: FieldType
pkField = Binary 340282366920938463463374607431768211457

inversePK :: Field -> Comp Field
inversePK x = do
  out <- freshVarField
  h <- (freshVarUInt :: Comp (UInt 8)) >>= toField
  m <- (freshVarUInt :: Comp (UInt 1)) >>= toField
  assert $ 1 `eq` (x * out + 283 * h + m)
  assert $ 0 `eq` ((out + 256 * x + 65536 * h + 16777216 * (1 + m)) * m)
  return out
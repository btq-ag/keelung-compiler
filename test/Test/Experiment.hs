{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

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

  it "283$2 + $3 = 1 (Bianry 340282366920938463463374607431768211457)" $ do
    let polynomial = case Poly.buildEither 1 [(2, 283), (3, 1)] of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly (Prime 340282366920938463463374607431768211457)
    let actual = BinRep.findAssignment 128 (const True) polynomial
    let expected = Just (IntMap.fromList [(2, False), (3, True)])
    actual `shouldBe` expected

testInversePK :: Integer -> Integer -> IO ()
testInversePK inputs expected = do
  actual <- solveOutput pkField (input Public >>= inversePK) [inputs] []
  actual `shouldBe` [expected]

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
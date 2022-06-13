{-# LANGUAGE DataKinds #-}
{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Basic where

import qualified AggregateSignature.Program
import AggregateSignature.Util
import Keelung.Compiler
import Keelung.Monad
import Keelung.Syntax
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import Keelung.Compiler.Constraint (cadd)
import Keelung.Field (GF181)
import Data.Typeable (Typeable)

--------------------------------------------------------------------------------

assertToBe42 :: Comp GF181 (Expr 'Unit GF181)
assertToBe42 = do
  x <- inputVar
  assert $ Var x `Eq` 42 
  return unit

constant1 :: Comp GF181 (Expr 'Num GF181)
constant1 = do
  return $ 1 + 1

identity :: Comp GF181 (Expr 'Num GF181)
identity = Var <$> inputVar

identityB :: Comp GF181 (Expr 'Bool GF181)
identityB = Var <$> inputVar

add3 :: Comp GF181 (Expr 'Num GF181)
add3 = do
  x <- inputVar
  return $ Var x + 3

-- takes an input and see if its equal to 3
eq1 :: Comp GF181 (Expr 'Bool GF181)
eq1 = do
  x <- inputVar
  return $ Var x `Eq` 3

cond :: Comp GF181 (Expr 'Num GF181)
cond = do
  x <- inputVar
  if Var x `Eq` 3
    then return 12
    else return 789

loop1 :: Comp GF181 (Expr 'Num GF181)
loop1 = do
  arr <- inputArray 4
  reduce 0 [0 .. 3] $ \accum i -> do
    x <- access i arr
    return $ accum + Var x

assert1 :: Comp GF181 (Expr 'Num GF181)
assert1 = do
  x <- inputVar
  assert (Var x `Eq` 3)
  return $ Var x

loop2 :: Comp GF181 ()
loop2 = do
  arr <- inputArray 2
  arr2 <- inputArray 2
  assertArrayEqual 2 arr (arr2 :: (Ref ('A ('V 'Num))))

make :: (GaloisField n, Integral n) => Int -> Int -> Param n
make dim n = makeParam dim n 42 $ Settings True True True

aggSig :: Int -> Int -> Comp GF181 (Expr 'Unit GF181)
aggSig dim n = AggregateSignature.Program.aggregateSignature (make dim n)

p :: Param GF181
p = makeParam 1 1 42 $ Settings False True False

inputs :: [GF181]
inputs = genInputFromParam p

a :: Comp GF181 (Expr 'Unit GF181)
a = checkSize 1 1

-- components of aggregate signature
checkAgg :: Int -> Int -> Comp GF181 (Expr 'Unit GF181)
checkAgg dim n = AggregateSignature.Program.checkAgg (make dim n)

-- -- #2
checkSize :: Int -> Int -> Comp GF181 (Expr 'Unit GF181)
checkSize dim n = AggregateSignature.Program.checkSize (make dim n)

-- -- #3
checkLength :: Int -> Int -> Comp GF181 (Expr 'Unit GF181)
checkLength dim n = AggregateSignature.Program.checkLength (make dim n)

--------------------------------------------------------------------------------

bench :: Typeable kind => Comp GF181 (Expr kind GF181) -> Settings -> Int -> Int -> Either (Error GF181) (Int, Int, Int)
bench program settings dimension n = do
  let input = genInputFromParam (makeParam dimension n 42 settings)
  cs <- comp program -- before optimisation (only constant propagation)
  cs' <- optm program -- after optimisation (constant propagation + constraint set reduction)
  cs'' <- optmWithInput program input -- after optimisation (constant propagation + constraint set reduction with input)
  return
    ( numberOfConstraints cs,
      numberOfConstraints cs',
      numberOfConstraints cs''
    )

-- #1
runAggSig :: Int -> Int -> Either (Error GF181) (Int, Int, Int)
runAggSig dimension n = do
  let settings = Settings True True True
  bench (aggSig dimension n) settings dimension n

-- -- #1
-- runCheckSig :: Int -> Int -> Either String (Int, Int, Int)
-- runCheckSig dimension n = do
--   let settings = Settings True False False
--   bench (checkSig dimension n) settings dimension n

-- -- #2 !!
-- runCheckSigSize :: Int -> Int -> Either String (Int, Int, Int)
-- runCheckSigSize dimension n = do
--   let settings = Settings False True False
--   bench (checkSigSize dimension n) settings dimension n

-- -- #3 !!
-- runCheckLength :: Int -> Int -> Either String (Int, Int, Int)
-- runCheckLength dimension n = do
--   let settings = Settings False False True
--   bench (checkSigLength dimension n) settings dimension n

cs1 :: ConstraintSystem GF181 
cs1 =
  ConstraintSystem
    { csConstraints =
        Set.fromList
          [ cadd 0 [(0, 4972), (1, 10582), (16, -1)],
            cadd 0 [(0, 10582), (1, 7317), (17, -1)],
            cadd 0 [(2, 3853), (3, 4216), (15, -1)],
            cadd 0 [(2, 8073), (3, 3853), (14, -1)],
            cadd 0 [(4, 1), (8, 12289), (17, -1)],
            cadd 0 [(5, 1), (9, 12289), (16, -1)],
            cadd 0 [(6, 1), (10, 12289), (15, -1)],
            cadd 0 [(7, 1), (11, 12289), (14, -1)],
            cadd 0 [(4, 1), (6, 1), (13, -1)],
            cadd 0 [(5, 1), (7, 1), (12, -1)],
            cadd 10623 [(13, -1)],
            cadd 11179 [(12, -1)]
          ],
      csBooleanInputVarConstraints = mempty,
      csVars = IntSet.fromList [0 .. 17],
      csInputVars = IntSet.fromList [0 .. 11],
      csOutputVar = Nothing
    }
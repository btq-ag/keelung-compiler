{-# LANGUAGE DataKinds #-}
{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Basic where

import qualified AggregateSignature.Program
import AggregateSignature.Util
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Keelung.Compiler
import Keelung.Compiler.Constraint (cadd)
import Keelung.Field (GF181)
import Keelung.Monad
import Keelung.Syntax
import Keelung (Compilable)
import Control.Monad (forM_)

--------------------------------------------------------------------------------

assertToBe42 :: Comp GF181 (Expr 'Unit GF181)
assertToBe42 = do
  x <- input
  assert $ x `Eq` 42
  return unit

constant1 :: Comp GF181 (Expr 'Num GF181)
constant1 = do
  return $ 1 + 1

identity :: Comp GF181 (Expr 'Num GF181)
identity = input

identityB :: Comp GF181 (Expr 'Bool GF181)
identityB = input

add3 :: Comp GF181 (Expr 'Num GF181)
add3 = do
  x <- input
  return $ x + 3

-- takes an input and see if its equal to 3
eq1 :: Comp GF181 (Expr 'Bool GF181)
eq1 = do
  x <- input
  return $ x `Eq` 3

cond' :: Comp GF181 (Expr 'Num GF181)
cond' = do
  x <- input
  return $ cond (x `Eq` 3) 12 789

summation :: Comp GF181 (Expr 'Num GF181)
summation = do
  arr <- inputs 4
  reduce 0 [0 .. 3] $ \accum i -> do
    x <- access arr i
    return $ accum + x

summation2 :: Comp GF181 (Expr 'Unit GF181)
summation2 = do
  arr <- inputs 4
  sumA <- reduce 0 [0 .. 3] $ \accum i -> do
    x <- access arr i
    return $ accum + x
  sumB <- reduce 0 [3, 2, 1, 0] $ \accum i -> do
    x <- access arr i
    return $ accum + x
  assert $ sumA `Eq` sumB
  return unit 

assertArraysEqual :: Comp GF181 (Expr 'Unit GF181)
assertArraysEqual = do 
  arrA <- inputs 4
  arrB <- inputs 4
  forM_ [0 .. 3] $ \i -> do
    x <- access arrA i
    y <- access arrB i
    assert $ x `Eq` y
  return unit 

assertArraysEqual2 :: Comp GF181 (Expr 'Unit GF181)
assertArraysEqual2 = do 
  arr <- inputs2 2 4 
  forM_ [0 .. 1] $ \i -> do
    forM_ [0 .. 3] $ \j -> do
      x <- access2 arr (i, j)
      y <- access2 arr (i, j)
      assert $ x `Eq` y
  return unit 

every :: Comp GF181 (Expr 'Bool GF181)
every = do
  arr <- inputs 4
  reduce true [0 .. 3] $ \accum i -> do
    x <- access arr i
    return $ accum `And` x

assert1 :: Comp GF181 (Expr 'Num GF181)
assert1 = do
  x <- input
  assert (x `Eq` 3)
  return x

-- loop2 :: Comp GF181 ()
-- loop2 = do
--   arr <-  inputs 2
--   arr2 <-  inputs 2
--   assertArrayEqual 2 arr (arr2 :: (Ref ('A ('V 'Num))))

make :: (GaloisField n, Integral n) => Int -> Int -> Param n
make dim n = makeParam dim n 42 $ Settings True True True

aggSig :: Int -> Int -> Comp GF181 (Expr 'Unit GF181)
aggSig dim n = AggregateSignature.Program.aggregateSignature (make dim n)

p :: Param GF181
p = makeParam 1 1 42 $ Settings False True False

-- inputs :: [GF181]
-- inputs = genInputFromParam p

a1 :: Comp GF181 (Expr 'Unit GF181)
a1 = checkAgg 1 1

a2 :: Comp GF181 (Expr 'Unit GF181)
a2 = checkSize 1 1

agg :: Comp GF181 (Expr 'Unit GF181)
agg = do 
  a1 >> a2

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

bench :: Compilable t => Comp GF181 (Expr t GF181) -> Settings -> Int -> Int -> Either (Error GF181) (Int, Int, Int)
bench program settings dimension n = do
  let inputVal = genInputFromParam (makeParam dimension n 42 settings)
  cs <- comp program -- before optimisation (only constant propagation)
  cs' <- optm program -- after optimisation (constant propagation + constraint set reduction)
  cs'' <- optmWithInput program inputVal -- after optimisation (constant propagation + constraint set reduction with input)
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
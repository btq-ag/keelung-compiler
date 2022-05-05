{-# LANGUAGE DataKinds #-}
{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Basic where

import qualified AggregateSignature.Program
import AggregateSignature.Util
import Keelung

--------------------------------------------------------------------------------

constant1 :: Comp GF181 (Expr 'Num GF181)
constant1 = do
  return $ 1 + 1

identity :: Comp GF181 (Expr 'Num GF181)
identity = Var <$> freshInput

identityB :: Comp GF181 (Expr 'Bool GF181)
identityB = Var <$> freshInput

add3 :: Comp GF181 (Expr 'Num GF181)
add3 = do
  x <- freshInput
  return $ Var x + 3

-- takes an input and see if its equal to 3
eq1 :: Comp GF181 (Expr 'Bool GF181)
eq1 = do
  x <- freshInput
  return $ Var x `Eq` 3

cond :: Comp GF181 (Expr 'Num GF181)
cond = do
  x <- freshInput
  if Var x `Eq` 3
    then return 12
    else return 789

loop1 :: Comp GF181 (Expr 'Num GF181)
loop1 = do
  arr <- freshInputs 4
  reduce 0 [0 .. 3] $ \accum i -> do
    x <- access arr i
    return $ accum + Var x

assert1 :: Comp GF181 (Expr 'Num GF181)
assert1 = do
  x <- freshInput
  assert (Var x `Eq` 3)
  return $ Var x

loop2 :: Comp GF181 ()
loop2 = do
  arr <- freshInputs 2
  arr2 <- freshInputs 2
  arrayEq 2 arr (arr2 :: (Ref ('A ('V 'Num))))

make :: (GaloisField n, Integral n) => Int -> Int -> Param n
make dim n = makeParam dim n 42 $ Settings True True True

aggSig :: Int -> Int -> Comp GF181 ()
aggSig dim n = AggregateSignature.Program.aggregateSignature (make dim n)

-- components of aggregate signature
checkAgg :: Int -> Int -> Comp GF181 ()
checkAgg dim n = AggregateSignature.Program.checkAgg (make dim n)

-- -- #2
checkSize :: Int -> Int -> Comp GF181 ()
checkSize dim n = AggregateSignature.Program.checkSize (make dim n)

-- -- #3
checkLength :: Int -> Int -> Comp GF181 ()
checkLength dim n = AggregateSignature.Program.checkLength (make dim n)

--------------------------------------------------------------------------------

bench :: Compilable GF181 a => Comp GF181 a -> Settings -> Int -> Int -> Either String (Int, Int, Int)
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
runAggSig :: Int -> Int -> Either String (Int, Int, Int)
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

--------------------------------------------------------------------------------

-- elaborate & erase type & propagate constants
-- cp :: (Erase ty, Num n) => Comp n (Expr ty n) -> Either String (TypeErased n)
-- cp program = ConstantPropagation.run <$> erase program

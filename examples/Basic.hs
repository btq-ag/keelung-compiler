{-# LANGUAGE DataKinds #-}
{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Basic where

import qualified AggregateSignature.Program
import AggregateSignature.Util
import Control.Monad (forM_)
import qualified Data.Set as Set
import Keelung
import Keelung.Compiler
  ( ConstraintSystem (..),
    Error,
    numberOfConstraints,
    optimizeWithInput,
  )
import qualified Keelung.Compiler as Compiler
import Keelung.Compiler.Constraint (cadd)
import Keelung.Types (VarCounters(..))

--------------------------------------------------------------------------------

assertToBe42 :: Comp ()
assertToBe42 = do
  x <- input
  assert $ x `Eq` 42

constant1 :: Comp Number
constant1 =
  return $ 1 + 1

identity :: Comp Number
identity = input

identityB :: Comp Boolean
identityB = input

add3 :: Comp Number
add3 = do
  x <- input
  return $ x + 3

-- takes an input and see if its equal to 3
eq1 :: Comp Boolean
eq1 = do
  x <- input
  return $ x `Eq` 3

cond' :: Comp Number
cond' = do
  x <- input
  return $ cond (x `Eq` 3) 12 789

summation :: Comp Number
summation = do
  arr <- inputs 4
  reduce 0 [0 .. 3] $ \accum i -> do
    let x = access arr i
    return $ accum + x

summation2 :: Comp ()
summation2 = do
  arr <- inputs 4
  sumA <- reduce 0 [0 .. 3] $ \accum i -> do
    let x = access arr i
    return $ accum + x
  sumB <- reduce 0 [3, 2, 1, 0] $ \accum i -> do
    let x = access arr i
    return $ accum + x
  assert $ sumA `Eq` sumB

assertArraysEqual :: Comp ()
assertArraysEqual = do
  arrA <- inputs 4
  arrB <- inputs 4
  forM_ [0 .. 3] $ \i -> do
    let x = access arrA i
    let y = access arrB i
    assert $ x `Eq` y

assertArraysEqual2 :: Comp ()
assertArraysEqual2 = do
  arr <- inputs2 2 4
  forM_ [0 .. 1] $ \i ->
    forM_ [0 .. 3] $ \j -> do
      let x = access2 arr (i, j)
      let y = access2 arr (i, j)
      assert $ x `Eq` y

every :: Comp Boolean
every = do
  arr <- inputs 4
  return $ foldl And true (fromArray arr)

assert1 :: Comp Number
assert1 = do
  x <- input
  assert (x `Eq` 3)
  return x

array1D :: Int -> Comp ()
array1D n = do
  xs <- inputs n
  expected <- inputs n
  mapM_ assert (zipWith Eq (map (\x -> x * x) $ fromArray xs) (fromArray expected))

array2D :: Int -> Int -> Comp ()
array2D n m = do
  xs <- inputs2 n m
  expected <- inputs2 n m

  forM_ [0 .. n - 1] $ \i ->
    forM_ [0 .. m - 1] $ \j -> do
      let x = access2 xs (i, j)
      let x' = access2 expected (i, j)
      assert (x' `Eq` (x * x))

toArray1 :: Comp ()
toArray1 = do
  xss <- inputs2 2 4
  let yss = toArray [toArray [0, 1, 2, 3], toArray [4, 5, 6, 7]]

  forM_ [0 .. 1] $ \i -> do
    let xs = access xss i
    let ys = access yss i
    forM_ [0 .. 3] $ \j -> do
      let x = access xs j
      let y = access ys j
      assert $ x `Eq` y

make :: Int -> Int -> Param GF181
make dim n = makeParam dim n 42 $ Settings True True True

aggSig :: Int -> Int -> Comp ()
aggSig dim n = AggregateSignature.Program.aggregateSignature (make dim n)

p :: Param GF181
p = makeParam 1 1 42 $ Settings False True False

-- inputs :: [GF181]
-- inputs = genInputFromParam p

a1 :: Comp ()
a1 = checkAgg 1 1

a2 :: Comp ()
a2 = checkSize 1 1

a3 :: Comp ()
a3 = checkLength 1 1

agg :: Comp ()
agg = a1 >> a2 >> a3

-- components of aggregate signature
checkAgg :: Int -> Int -> Comp ()
checkAgg dim n = AggregateSignature.Program.checkAgg (make dim n)

-- -- #2
checkSize :: Int -> Int -> Comp ()
checkSize dim n = AggregateSignature.Program.checkSize (make dim n)

-- -- #3
checkLength :: Int -> Int -> Comp ()
checkLength dim n = AggregateSignature.Program.checkLength (make dim n)

--------------------------------------------------------------------------------

bench :: Elaborable t => Comp t -> Settings -> Int -> Int -> Either (Error GF181) (Int, Int, Int)
bench program settings dimension n = do
  let inputVal = genInputFromParam (makeParam dimension n 42 settings)
  cs <- Compiler.compileO0 program -- before optimisation (only constant propagation)
  cs' <- Compiler.compileO1 program -- after optimisation (constant propagation + constraint set reduction)
  cs'' <- optimizeWithInput program inputVal -- after optimisation (constant propagation + constraint set reduction with input)
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
        Set.fromList $
          concat
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
      csBoolVars = mempty,
      csVarCounters = VarCounters 12 0 0 0 5
    }

xorLists :: Comp Boolean
xorLists = do
  let xs = toArray [false]
  let ys = toArray [true]
  let x = access xs 0
  let y = access ys 0
  let actual = toArray [x `Xor` y]
  let expected = toArray [true]
  return $
    foldl
      ( \acc i ->
          let a = access actual i
              b = access expected i
           in acc `And` (a `BEq` b)
      )
      true
      [0]

outOfBound :: Comp ()
outOfBound = do
  let xs = toArray [true]
  let _ = access xs 2
  return ()

emptyArray :: Comp ()
emptyArray = do
  let _ = toArray [] :: Arr Boolean
  return ()

dupArray :: Comp Number
dupArray = do
  x <- input
  let xs = toArray [x, x]
  return $ access xs 1

returnArray :: Comp (Arr Number)
returnArray = do
  x <- input
  y <- input
  return $ toArray [x, y]

returnArray2 :: Comp (Arr Number)
returnArray2 = do
  x <- input
  return $ toArray [x, x * 2]

toArrayM1 :: Comp (ArrM Boolean)
toArrayM1 = toArrayM [false]

birthday :: Comp Boolean
birthday = do
  -- these inputs are private witnesses
  _hiddenYear <- inputNum
  hiddenMonth <- input
  hiddenDate <- input
  -- these inputs are public inputs
  month <- input
  date <- input

  return $ (hiddenMonth `Eq` month) `And` (hiddenDate `Eq` date)

chainingAND :: Int -> Comp Boolean
chainingAND n = foldl And true <$> inputs n

chainingOR :: Int -> Comp Boolean
chainingOR n = foldl Or false <$> inputs n

toBool :: Comp Boolean
toBool = ToBool <$> input

bitsVal :: Comp (Arr Boolean)
bitsVal = do 
  x <- input
  let c = 3
  return $ toArray [x ! 0, c ! 1, c ! 2]

{-# LANGUAGE DataKinds #-}
{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Basic where

import qualified AggregateSignature.Program
import AggregateSignature.Util
import Control.Monad (forM_)
import Keelung
import Keelung.Compiler
  ( Error,
    numberOfConstraints,
    optimizeWithInput,
  )
import qualified Keelung.Compiler as Compiler

--------------------------------------------------------------------------------

assertToBe42 :: Comp ()
assertToBe42 = do
  x <- inputNum
  assert $ x `eq` 42

-- | A program that expects the second input to be the square of the first input
-- This program returns no output
assertSquare :: Comp ()
assertSquare = do
  x <- inputNum
  y <- input
  assert ((x * x) `eq` y)

constant1 :: Comp Number
constant1 =
  return $ 1 + 1

identity :: Comp Number
identity = input

identityB :: Comp Boolean
identityB = input

add3 :: Comp Number
add3 = do
  x <- inputNum
  return $ x + 3

-- takes an input and see if its equal to 3
eq1 :: Comp Boolean
eq1 = do
  x <- inputNum
  return $ x `eq` 3

cond' :: Comp Number
cond' = do
  x <- inputNum
  return $ cond (x `eq` 3) 12 789

summation :: Comp Number
summation = do
  arr <- inputs 4
  reduce 0 [0 .. 3] $ \accum i -> do
    let x = access arr i
    return $ accum + x

summation2 :: Comp ()
summation2 = do
  arr <- inputs 4 :: Comp (Arr Number)
  sumA <- reduce 0 [0 .. 3] $ \accum i -> do
    let x = access arr i
    return $ accum + x
  sumB <- reduce 0 [3, 2, 1, 0] $ \accum i -> do
    let x = access arr i
    return $ accum + x
  assert $ sumA `eq` sumB

assertArraysEqual :: Comp ()
assertArraysEqual = do
  arrA <- inputs 4 :: Comp (Arr Number)
  arrB <- inputs 4
  forM_ [0 .. 3] $ \i -> do
    let x = access arrA i
    let y = access arrB i
    assert $ x `eq` y

assertArraysEqual2 :: Comp ()
assertArraysEqual2 = do
  arr <- inputs2 2 4 :: Comp (Arr (Arr Number))
  forM_ [0 .. 1] $ \i ->
    forM_ [0 .. 3] $ \j -> do
      let x = access2 arr (i, j)
      let y = access2 arr (i, j)
      assert $ x `eq` y

every :: Comp Boolean
every = do
  arr <- inputs 4
  return $ foldl And true (fromArray arr)

assert1 :: Comp Number
assert1 = do
  x <- input
  assert (x `eq` 3)
  return x

array1D :: Int -> Comp ()
array1D n = do
  xs <- inputs n :: Comp (Arr Number)
  expected <- inputs n
  mapM_ assert (zipWith eq (map (\x -> x * x) $ fromArray xs) (fromArray expected))

array2D :: Int -> Int -> Comp ()
array2D n m = do
  xs <- inputs2 n m :: Comp (Arr (Arr Number))
  expected <- inputs2 n m

  forM_ [0 .. n - 1] $ \i ->
    forM_ [0 .. m - 1] $ \j -> do
      let x = access2 xs (i, j)
      let x' = access2 expected (i, j)
      assert (x' `eq` (x * x))

toArray1 :: Comp ()
toArray1 = do
  xss <- inputs2 2 4 :: Comp (Arr (Arr Number))
  let yss = toArray [toArray [0, 1, 2, 3], toArray [4, 5, 6, 7]]

  forM_ [0 .. 1] $ \i -> do
    let xs = access xss i
    let ys = access yss i
    forM_ [0 .. 3] $ \j -> do
      let x = access xs j
      let y = access ys j
      assert $ x `eq` y

make :: Int -> Int -> Param GF181
make dim n = makeParam dim n 42 $ Settings True True True

aggSig :: Int -> Int -> Comp ()
aggSig dim n = AggregateSignature.Program.aggregateSignature (make dim n)

aggSigInput :: Int -> Int -> [Integer]
aggSigInput dim n = map toInteger $ genInputFromParam (makeParam dim n 42 $ Settings True True True)

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

bench :: Encode t => Comp t -> Settings -> Int -> Int -> Either (Error GF181) (Int, Int, Int)
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
           in acc `And` (a `eq` b)
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
  hiddenMonth <- inputNum
  hiddenDate <- inputNum
  -- these inputs are public inputs
  month <- input
  date <- input

  return $ (hiddenMonth `eq` month) `And` (hiddenDate `eq` date)

chainingAND :: Int -> Comp Boolean
chainingAND n = foldl And true <$> inputs n

chainingOR :: Int -> Comp Boolean
chainingOR n = foldl Or false <$> inputs n

-- bits1 :: Comp (Arr Boolean)
-- bits1 = do
--   x <- inputNum
--   y <- inputNum
--   return $ toArray [(x !!! 0) `And` (y !!! (-1))]

bitValueU :: Comp (Arr Boolean)
bitValueU = do
  let c = 3 :: UInt 4
  return $ toArray [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]

bitTestInputVarU :: Comp (Arr Boolean)
bitTestInputVarU = do
  x <- inputUInt @4
  return $ toArray [x !!! (-1), x !!! 0, x !!! 1, x !!! 2, x !!! 3, x !!! 4]

notU :: Comp (UInt 4)
notU = do
      x <- inputUInt @4
      return $ complement x

neqU :: Comp Boolean
neqU = do
      x <- inputUInt @4
      y <- inputUInt @4
      return $ x `neq` y

bits2 :: Comp Boolean
bits2 = do
  x <- inputUInt @4
  y <- inputUInt @4
  z <- inputUInt @4
  w <- inputUInt @4
  return $ (x .&. y .&. z .&. w) !!! 0

-- Formula: (0°C × 9/5) + 32 = 32°F
tempConvert :: Comp Number
tempConvert = do
  toFahrenheit <- input
  degree <- input
  return $
    cond
      toFahrenheit
      (degree * 9 / 5 + 32)
      (degree - 32 * 5 / 9)

mixed :: Comp Number
mixed = do
  boolean <- input
  number <- input
  return $ fromBool boolean + number * 2

addU :: Comp (UInt 4)
addU = do
  x <- inputUInt @4
  y <- inputUInt @4
  return $ x + y + x

mulU :: Comp (UInt 4)
mulU = do
  x <- inputUInt @4
  y <- inputUInt @4
  return $ x * y

bitwise :: Comp (Arr Boolean)
bitwise = do
  x <- inputUInt @4
  y <- inputUInt @4
  return $
    toArray
      [ (x .&. y) !!! 0,
        (x .|. y) !!! 1,
        (x .^. y) !!! 2,
        complement x !!! 3
      ]

rotateAndBitTest :: Comp (Arr Boolean)
rotateAndBitTest = do
  x <- inputUInt @4
  y <- inputUInt @4
  return $
    toArray
      [ (x `rotate` 0) !!! 0,
        (x `rotate` 1) !!! 1,
        (x `rotate` (-1)) !!! 1,
        ((x .^. y) `rotate` 1) !!! 2
      ]

rotateOnly :: Comp (Arr (UInt 4))
rotateOnly = do
  x <- inputUInt @4
  let constant = 3 :: UInt 4
  -- y <- inputUInt @4
  return $
    toArray
      [ x `rotate` 0,
        constant `rotate` 3,
        constant `rotate` (-2),
        x `rotate` 1 `rotate` 1,
        (x + x) `rotate` 1
      ]

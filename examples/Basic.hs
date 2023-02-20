{-# LANGUAGE DataKinds #-}
{-# HLINT ignore "Use <&>" #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use head" #-}

module Basic where

import AggregateSignature.Program qualified
import AggregateSignature.Util
import Control.Monad (forM_)
import Keelung
import Keelung.Compiler
  ( Error,
    numberOfConstraints,
    optimizeWithInput,
  )
import Keelung.Compiler qualified as Compiler

--------------------------------------------------------------------------------

assertToBe42 :: Comp ()
assertToBe42 = do
  x <- inputField Public
  assert $ x `eq` 42

-- | A program that expects the second input to be the square of the first input
-- This program returns no output
assertSquare :: Comp ()
assertSquare = do
  x <- inputField Public
  y <- input Public
  assert ((x * x) `eq` y)

constant1 :: Comp Field
constant1 =
  return $ 1 + 1

identity :: Comp Field
identity = input Public

identityB :: Comp Boolean
identityB = input Public

-- takes an input and see if its equal to 3
eq1 :: Comp Boolean
eq1 = do
  x <- inputField Public
  return $ x `eq` 3

cond' :: Comp Field
cond' = do
  x <- inputField Public
  return $ cond (x `eq` 3) 12 789

summation :: Comp Field
summation = do
  arr <- inputList Public 4
  reduce 0 [0 .. 3] $ \accum i -> do
    let x = arr !! i
    return $ accum + x

summation2 :: Comp ()
summation2 = do
  arr <- inputList Public 4 :: Comp [Field]
  sumA <- reduce 0 [0 .. 3] $ \accum i -> do
    let x = arr !! i
    return $ accum + x
  sumB <- reduce 0 [3, 2, 1, 0] $ \accum i -> do
    let x = arr !! i
    return $ accum + x
  assert $ sumA `eq` sumB

assertArraysEqual :: Comp ()
assertArraysEqual = do
  arrA <- inputList Public 4 :: Comp [Field]
  arrB <- inputList Public 4
  forM_ [0 .. 3] $ \i -> do
    let x = arrA !! i
    let y = arrB !! i
    assert $ x `eq` y

assertArraysEqual2 :: Comp ()
assertArraysEqual2 = do
  arr <- inputList2 Public 2 4 :: Comp [[Field]]
  forM_ [0 .. 1] $ \i ->
    forM_ [0 .. 3] $ \j -> do
      let x = arr !! i !! j
      let y = arr !! i !! j
      assert $ x `eq` y

every :: Comp Boolean
every = do
  arr <- inputList Public 4
  return $ foldl And true arr

assert1 :: Comp ()
assert1 = do
  x <- inputField Public
  assert (x `eq` 3)

array1D :: Int -> Comp ()
array1D n = do
  xs <- inputList Public n :: Comp [Field]
  expected <- inputList Public n
  mapM_ assert (zipWith eq (map (\x -> x * x) xs) expected)

array2D :: Int -> Int -> Comp ()
array2D n m = do
  xs <- inputList2 Public n m :: Comp [[Field]]
  expected <- inputList2 Public n m

  forM_ [0 .. n - 1] $ \i ->
    forM_ [0 .. m - 1] $ \j -> do
      let x = xs !! i !! j
      let x' = expected !! i !! j
      assert (x' `eq` (x * x))

toArray1 :: Comp ()
toArray1 = do
  xss <- inputList2 Public 2 4 :: Comp [[Field]]
  let yss = [[0, 1, 2, 3], [4, 5, 6, 7]]

  forM_ [0 .. 1] $ \i -> do
    let xs = xss !! i
    let ys = yss !! i
    forM_ [0 .. 3] $ \j -> do
      let x = xs !! j
      let y = ys !! j
      assert $ x `eq` y

make :: Int -> Int -> Param GF181
make dim n = makeParam dim n 42 $ Settings True True True

aggSig :: Int -> Int -> Comp ()
aggSig dim n = AggregateSignature.Program.aggregateSignature (make dim n)

aggSigInput :: Int -> Int -> [Integer]
aggSigInput dim n = map toInteger $ genInputFromParam (makeParam dim n 42 $ Settings True True True)

p :: Param GF181
p = makeParam 1 1 42 $ Settings False True False

-- inputList :: [GF181]
-- inputList = genInputFromParam p

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
  let xs = [false]
  let ys = [true]
  let x = xs !! 0
  let y = ys !! 0
  let actual = [x `Xor` y]
  let expected = [true]
  return $
    foldl
      ( \acc i ->
          let a = actual !! i
              b = expected !! i
           in acc `And` (a `eq` b)
      )
      true
      [0]

outOfBound :: Comp ()
outOfBound = do
  let xs = [true]
  let _ = xs !! 2
  return ()

emptyArray :: Comp ()
emptyArray = do
  let _ = [] :: [Boolean]
  return ()

dupArray :: Comp Field
dupArray = do
  x <- input Public
  let xs = [x, x]
  return $ xs !! 1

dupList :: Comp [Field]
dupList = do
  x <- input Public
  return [x, x]

returnArray :: Comp [Field]
returnArray = do
  x <- input Public
  y <- input Public
  return [x, y]

returnArray2 :: Comp [Field]
returnArray2 = do
  x <- input Public
  return [x, x * 2]

toArrayM1 :: Comp (ArrM Boolean)
toArrayM1 = toArrayM [false]

birthday :: Comp Boolean
birthday = do
  -- these inputList are private witnesses
  _hiddenYear <- inputField Public
  hiddenMonth <- inputField Public
  hiddenDate <- inputField Public
  -- these inputList are public inputList
  month <- input Public
  date <- input Public

  return $ (hiddenMonth `eq` month) `And` (hiddenDate `eq` date)

chainingAND :: Int -> Comp Boolean
chainingAND n = foldl And true <$> inputList Public n

chainingOR :: Int -> Comp Boolean
chainingOR n = foldl Or false <$> inputList Public n

bitValueU :: Comp [Boolean]
bitValueU = do
  let c = 3 :: UInt 4
  return [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]

bitTestVarUI :: Comp [Boolean]
bitTestVarUI = do
  x <- inputUInt @4 Public
  return [x !!! (-1), x !!! 0, x !!! 1, x !!! 2, x !!! 3, x !!! 4]

notU :: Comp (UInt 4)
notU = do
  x <- inputUInt @4 Public
  return $ complement x

neqU :: Comp Boolean
neqU = do
  x <- inputUInt @4 Public
  y <- inputUInt @4 Public
  return $ x `neq` y

bits2 :: Comp Boolean
bits2 = do
  x <- inputUInt @4 Public
  y <- inputUInt @4 Public
  z <- inputUInt @4 Public
  w <- inputUInt @4 Public
  return $ (x .&. y .&. z .&. w) !!! 0

bitTestsOnBtoU :: Comp [Boolean]
bitTestsOnBtoU = do
  -- output | input | intermediate
  -- bb       b       rrrrrrrruu
  -- 01       2       3456789012
  x <- input Public
  let u = BtoU x :: UInt 4
  return [u !!! 0, u !!! 1]

-- Formula: (0°C × 9/5) + 32 = 32°F
tempConvert :: Comp Field
tempConvert = do
  toFahrenheit <- input Public
  degree <- input Public
  return $
    cond
      toFahrenheit
      (degree * 9 / 5 + 32)
      (degree - 32 * 5 / 9)

mixed :: Comp Field
mixed = do
  boolean <- input Public 
  number <- input Public 
  return $ BtoF boolean + number * 2

addU :: Comp (UInt 4)
addU = do
  x <- inputUInt @4 Public
  y <- inputUInt @4 Public
  return $ x + y + x

mulU :: Comp (UInt 4)
mulU = do
  x <- inputUInt @4 Public
  y <- inputUInt @4 Public
  return $ x * y

bitwise :: Comp [Boolean]
bitwise = do
  x <- inputUInt @4 Public
  y <- inputUInt @4 Public
  return
    [ (x .&. y) !!! 0,
      (x .|. y) !!! 1,
      (x .^. y) !!! 2,
      complement x !!! 3
    ]

arithU0 :: Comp (UInt 4)
arithU0 = do
  x <- inputUInt @4 Public
  y <- inputUInt @4 Public
  return $ x + y

rotateAndBitTest :: Comp [Boolean]
rotateAndBitTest = do
  x <- inputUInt @4 Public
  y <- inputUInt @4 Public
  return
    [ (x `rotate` 0) !!! 0,
      (x `rotate` 1) !!! 1,
      (x `rotate` (-1)) !!! 0,
      ((x .^. y) `rotate` 1) !!! 1
    ]

rotateOnly :: Comp [UInt 4]
rotateOnly = do
  x <- inputUInt @4 Public
  let constant = 3 :: UInt 4
  -- y <- inputUInt @4
  return
    [ x `rotate` 0,
      constant `rotate` 3,
      constant `rotate` (-2),
      x `rotate` 1 `rotate` 1,
      (x + x) `rotate` 1
    ]

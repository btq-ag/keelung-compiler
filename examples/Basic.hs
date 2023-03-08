module Basic where

import Control.Monad (forM_)
import Keelung

--------------------------------------------------------------------------------

assertToBe42 :: Comp ()
assertToBe42 = do
  x <- inputField Public
  assert $ x `eq` 42

identity :: Comp Field
identity = input Public

identityB :: Comp Boolean
identityB = input Public

-- takes an input and see if its equal to 3
eq1 :: Comp Boolean
eq1 = do
  x <- inputField Public
  return $ x `eq` 3

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

-- every :: Comp Boolean
-- every = do
--   arr <- inputList Public 4
--   return $ foldl And true arr

-- assert1 :: Comp ()
-- assert1 = do
--   x <- inputField Public
--   assert (x `eq` 3)

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

outOfBound :: Comp ()
outOfBound = do
  let xs = [true]
  let _ = xs !! 2
  return ()

emptyArray :: Comp ()
emptyArray = do
  let _ = [] :: [Boolean]
  return ()

chainingAND :: Int -> Comp Boolean
chainingAND n = foldl And true <$> inputList Public n

chainingOR :: Int -> Comp Boolean
chainingOR n = foldl Or false <$> inputList Public n

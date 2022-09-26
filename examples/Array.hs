{-# LANGUAGE DataKinds #-}

module Array where

import Control.Monad
import Keelung

echo :: Comp (Arr Number)
echo = inputs 4

modify :: Comp (Arr Number)
modify = do
  xs <- inputs 4 >>= thaw

  updateM xs 0 0
  updateM xs 1 1

  freeze xs

init :: Comp (Arr Boolean)
init = do
  let xs = toArray $ replicate 4 false
  return xs

initM :: Comp (ArrM Boolean)
initM = toArrayM $ replicate 4 false

initM2 :: Comp (Arr Boolean)
initM2 = do
  xs <- toArrayM $ replicate 4 false
  freeze xs

sharing :: Comp (Arr Number)
sharing = do
  x <- input
  let y = x * x * x * x
  return $ toArray [y, y]

sharing' :: Comp (Arr Number)
sharing' = do
  x <- input
  y <- reuse $ x * x * x * x
  return $ toArray [y, y]

fold :: Comp (Arr Number)
fold = do
  x <- input
  (xs, _) <-
    foldM 
      ( \(array, acc) _ ->
          return (array ++ [acc], acc * x)
      )
      ([], x)
      ([0 .. 10] :: [Int])
  return $ toArray xs

fold' :: Comp (Arr Number)
fold' = do
  x <- input
  (xs, _) <-
    foldM 
      ( \(array, acc) _ -> do 
            acc' <- reuse $ acc * x
            return (array ++ [acc'], acc')
      )
      ([], x)
      ([0 .. 10] :: [Int])
  return $ toArray xs
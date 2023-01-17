{-# LANGUAGE DeriveFunctor #-}

-- | Polynomial with variables generalized (unliked Poly which is limited to only Int)
module Keelung.Data.PolyG (PolyG, build, buildWithMap, unsafeBuild, view) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

data PolyG ref n = PolyG n (Map ref n)
  deriving (Eq, Functor, Ord)

instance (Show n, Ord n, Eq n, Num n, Show ref) => Show (PolyG ref n) where
  show (PolyG n xs)
    | n == 0 =
      if firstSign == " + "
        then concat restOfTerms
        else "- " <> concat restOfTerms
    | otherwise = concat (show n : termStrings)
    where
      (firstSign : restOfTerms) = termStrings

      termStrings = concatMap printTerm $ Map.toList xs
      -- return a pair of the sign ("+" or "-") and the string representation
      printTerm :: (Show n, Ord n, Eq n, Num n, Show ref) => (ref, n) -> [String]
      printTerm (x, c)
        | c == 0 = error "printTerm: coefficient of 0"
        | c == 1 = [" + ", show x]
        | c == -1 = [" - ", show x]
        | c < 0 = [" - ", show (Prelude.negate c) <> show x]
        | otherwise = [" + ", show c <> show x]

build :: (Ord ref, Num n, Eq n) => n -> [(ref, n)] -> Either n (PolyG ref n)
build c xs =
  let result = Map.filter (/= 0) $ Map.fromListWith (+) xs
   in if Map.null result
        then Left c
        else Right (PolyG c result)

buildWithMap :: (Ord ref, Num n, Eq n) => n -> Map ref n -> Either n (PolyG ref n)
buildWithMap c xs =
  let result = Map.filter (/= 0) xs
   in if Map.null result
        then Left c
        else Right (PolyG c result)

unsafeBuild :: (Ord ref, Eq n, Num n) => n -> [(ref, n)] -> PolyG ref n
unsafeBuild c xs =
  let result = Map.filter (/= 0) $ Map.fromListWith (+) xs
   in if Map.null result
        then error "[ panic ] PolyG.unsafeBuild: empty polynomial"
        else PolyG c result

view :: PolyG ref n -> (n, Map ref n)
view (PolyG c xs) = (c, xs)
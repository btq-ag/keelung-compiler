{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Polynomial with variables generalized (unliked Poly which is limited to only Int)
module Keelung.Data.PolyG (PolyG, View (..), build, buildWithMap, unsafeBuild, view, viewAsMap, insert, addConstant, multiplyBy, singleton, vars) where

import Control.DeepSeq (NFData)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)

data PolyG ref n = PolyG n (Map ref n)
  deriving (Eq, Functor, Ord, Generic, NFData)

instance (Show n, Ord n, Eq n, Num n, Show ref) => Show (PolyG ref n) where
  show (PolyG n xs)
    | n == 0 =
        if firstSign == " + "
          then concat restOfTerms
          else "- " <> concat restOfTerms
    | otherwise = concat (show n : firstSign : restOfTerms)
    where
      (firstSign, restOfTerms) = case concatMap printTerm $ Map.toList xs of
        [] -> error "[ panic ] Empty PolyG"
        (x' : xs') -> (x', xs')
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

singleton :: (Ord ref, Num n, Eq n) => n -> (ref, n) -> Either n (PolyG ref n)
singleton c (_, 0) = Left c
singleton c (x, coeff) = Right $ PolyG c (Map.singleton x coeff)

insert :: (Ord ref, Num n) => n -> (ref, n) -> PolyG ref n -> PolyG ref n
insert c' (x, coeff) (PolyG c xs) =
  let result = Map.insertWith (+) x coeff xs
   in if Map.null result
        then error "[ panic ] PolyG.insert: empty polynomial"
        else PolyG (c + c') result

addConstant :: Num n => n -> PolyG ref n -> PolyG ref n
addConstant c' (PolyG c xs) = PolyG (c + c') xs

-- | Multiply all coefficients and the constant by some non-zero number
multiplyBy :: (Num n, Eq n) => n -> PolyG ref n -> PolyG ref n
multiplyBy 0 _ = error "[ panic ] PolyG.multiplyBy: 0"
multiplyBy m (PolyG c xs) = PolyG (m * c) (Map.map (m *) xs)

unsafeBuild :: (Ord ref, Eq n, Num n) => n -> [(ref, n)] -> PolyG ref n
unsafeBuild c xs =
  let result = Map.filter (/= 0) $ Map.fromListWith (+) xs
   in if Map.null result
        then error "[ panic ] PolyG.unsafeBuild: empty polynomial"
        else PolyG c result

data View ref n = Monomial n (ref, n) | Binomial n (ref, n) (ref, n) | Polynomial n (Map ref n)
  deriving (Eq, Show)

view :: PolyG ref n -> View ref n
view (PolyG c xs) = case Map.toList xs of
  [] -> error "[ panic ] PolyG.view: empty polynomial"
  [(x, c')] -> Monomial c (x, c')
  [(x, c'), (y, c'')] -> Binomial c (x, c') (y, c'')
  _ -> Polynomial c xs

--   (n, (ref, n), [(ref, n)])
-- view (PolyG c xs) = case Map.toList xs of
--   [] -> error "[ panic ] PolyG.view: empty polynomial"
--   (x' : xs') -> (c, x', xs')

viewAsMap :: PolyG ref n -> (n, Map ref n)
viewAsMap (PolyG c xs) = (c, xs)

vars :: PolyG ref n -> [ref]
vars (PolyG _ xs) = Map.keys xs
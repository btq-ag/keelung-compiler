{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Polynomial made of Limbs
module Keelung.Data.PolyL
  ( PolyL,
    vars,
    vars',
    buildWithSeq,
    insert,
    singleton,
    addConstant,
    multiplyBy,
    merge,
    size,
    view,
  )
where

import Control.DeepSeq (NFData)
import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (toList)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung.Data.Reference

-- | Polynomial made of Limbs + a constant
data PolyL n = PolyL n (Seq (RefL, n))
  deriving (Eq, Functor, Ord, Generic, NFData)

instance (Show n, Ord n, Eq n, Num n) => Show (PolyL n) where
  show (PolyL n xs)
    | n == 0 =
        if firstSign == " + "
          then concat restOfTerms
          else "- " <> concat restOfTerms
    | otherwise = concat (show n : firstSign : restOfTerms)
    where
      (firstSign, restOfTerms) = case concatMap printTerm $ toList xs of
        [] -> error "[ panic ] Empty PolyG"
        (x' : xs') -> (x', xs')
      -- return a pair of the sign ("+" or "-") and the string representation
      printTerm :: (Show n, Ord n, Eq n, Num n) => (RefL, n) -> [String]
      printTerm (x, c)
        | c == 0 = error "printTerm: coefficient of 0"
        | c == 1 = [" + ", show x]
        | c == -1 = [" - ", show x]
        | c < 0 = [" - ", show (Prelude.negate c) <> show x]
        | otherwise = [" + ", show c <> show x]

buildWithSeq :: (Num n, Eq n) => n -> Seq (RefL, n) -> PolyL n
buildWithSeq = PolyL

singleton :: (Num n, Eq n) => n -> (RefL, n) -> Either n (PolyL n)
singleton c (_, 0) = Left c
singleton c (x, coeff) = Right $ PolyL c (Seq.singleton (x, coeff))

insert :: (Num n, Eq n) => n -> (RefL, n) -> PolyL n -> PolyL n
insert c' x (PolyL c xs) = PolyL (c + c') (x Seq.<| xs)

addConstant :: Num n => n -> PolyL n -> PolyL n
addConstant c' (PolyL c xs) = PolyL (c + c') xs

-- | Multiply all coefficients and the constant by some non-zero number
multiplyBy :: (Num n, Eq n) => n -> PolyL n -> Either n (PolyL n)
multiplyBy 0 _ = Left 0
multiplyBy m (PolyL c xs) = Right $ PolyL (m * c) (fmap (second (m *)) xs)

view :: PolyL n -> (n, Seq (RefL, n))
view (PolyL c xs) = (c, xs)

vars :: PolyL n -> Set RefU
vars (PolyL _ xs) = Set.fromList $ map (toRef . fst) (toList xs)
  where
    toRef :: RefL -> RefU
    toRef (RefL (Limb ref _ _ _) _) = ref

vars' :: PolyL n -> Set RefL
vars' (PolyL _ xs) = Set.fromList $ map fst (toList xs)

merge :: (Num n, Eq n) => PolyL n -> PolyL n -> PolyL n
merge (PolyL c1 xs1) (PolyL c2 xs2) = PolyL (c1 + c2) (xs1 <> xs2)

-- | Number of terms (including the constant)
size :: (Eq n, Num n) => PolyL n -> Int
size (PolyL c xs) = sum (fmap (widthOfRefL . fst) xs) + if c == 0 then 0 else 1
  where
    widthOfRefL :: RefL -> Int
    widthOfRefL (RefL limb _) = lmbWidth limb
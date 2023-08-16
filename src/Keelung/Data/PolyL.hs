{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Polynomial made of Limbs
module Keelung.Data.PolyL (PolyL (..), vars, buildWithSeq, size) where

import Control.DeepSeq (NFData)
import Data.Foldable (toList)
import Data.Sequence (Seq)
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

-- build :: (Num n, Eq n) => n -> [(Ref, n)] -> Either n (PolyG n)
-- build c xs =
--   let result = Map.filter (/= 0) $ Map.fromListWith (+) xs
--    in if Map.null result
--         then Left c
--         else Right (PolyG c result)

buildWithSeq :: (Num n, Eq n) => n -> Seq (RefL, n) -> PolyL n
buildWithSeq = PolyL

-- let result = Seq.filter ((/= 0) . snd) xs
--  in if Seq.null result
--       then Left c
--       else Right (PolyL c xs)

-- buildWithMap :: (Num n, Eq n) => n -> Map Ref n -> Either n (PolyG n)
-- buildWithMap c xs =
--   let result = Map.filter (/= 0) xs
--    in if Map.null result
--         then Left c
--         else Right (PolyG c result)

-- singleton :: (Num n, Eq n) => n -> (Ref, n) -> Either n (PolyG n)
-- singleton c (_, 0) = Left c
-- singleton c (x, coeff) = Right $ PolyG c (Map.singleton x coeff)

-- insert :: (Num n, Eq n) => n -> (Ref, n) -> PolyG n -> Either n (PolyG n)
-- insert c' (x, coeff) (PolyG c xs) =
--   let result = Map.filter (/= 0) $ Map.insertWith (+) x coeff xs
--    in if Map.null result
--         then Left (c + c')
--         else Right $ PolyG (c + c') result

-- addConstant :: Num n => n -> PolyG n -> PolyG n
-- addConstant c' (PolyG c xs) = PolyG (c + c') xs

-- -- | Multiply all coefficients and the constant by some non-zero number
-- multiplyBy :: (Num n, Eq n) => n -> PolyG n -> Either n (PolyG n)
-- multiplyBy 0 _ = Left 0
-- multiplyBy m (PolyG c xs) = Right $ PolyG (m * c) (Map.map (m *) xs)

-- -- | Negate a polynomial
-- negate :: (Num n, Eq n) => PolyG n -> PolyG n
-- negate (PolyG c xs) = PolyG (-c) (fmap Prelude.negate xs)

-- data View n = Monomial n (Ref, n) | Binomial n (Ref, n) (Ref, n) | Polynomial n (Map Ref n)
--   deriving (Eq, Show)

-- view :: PolyG n -> View n
-- view (PolyG c xs) = case Map.toList xs of
--   [] -> error "[ panic ] PolyG.view: empty polynomial"
--   [(x, c')] -> Monomial c (x, c')
--   [(x, c'), (y, c'')] -> Binomial c (x, c') (y, c'')
--   _ -> Polynomial c xs

-- viewAsMap :: PolyG n -> (n, Map Ref n)
-- viewAsMap (PolyG c xs) = (c, xs)

vars :: PolyL n -> Set RefU
vars (PolyL _ xs) = Set.fromList $ map (toRef . fst) (toList xs)
  where
    toRef :: RefL -> RefU
    toRef (RefL (Limb ref _ _ _) _) = ref

-- merge :: (Num n, Eq n) => PolyG n -> PolyG n -> Either n (PolyG n)
-- merge (PolyG c1 xs1) (PolyG c2 xs2) =
--   let result = Map.filter (/= 0) $ Map.unionWith (+) xs1 xs2
--    in if Map.null result
--         then Left (c1 + c2)
--         else Right (PolyG (c1 + c2) result)z

-- | Number of terms (including the constant)
size :: (Eq n, Num n) => PolyL n -> Int
size (PolyL c xs) = sum (fmap (widthOfRefL . fst) xs) + if c == 0 then 0 else 1
  where
    widthOfRefL :: RefL -> Int
    widthOfRefL (RefL limb _) = lmbWidth limb
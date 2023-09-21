{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Polynomial made of Limbs
module Keelung.Data.PolyL
  ( PolyL,
    vars,
    limbsSet,
    newL,
    newB,
    insertL,
    singletonL,
    addConstant,
    multiplyBy,
    size,
    view,
  )
where

import Control.DeepSeq (NFData)
import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung.Data.Reference
import Prelude hiding (null)

-- | Polynomial made of Limbs + a constant
data PolyL n = PolyL
  { -- | constant term
    polyConstant :: n,
    -- | (Limb, multiplier)
    polyLimbs :: [(Limb, n)],
    -- | (RefB, coefficient)
    polyBools :: Map RefB n
  }
  deriving (Eq, Functor, Ord, Generic, NFData)

instance (Semigroup n, Num n) => Semigroup (PolyL n) where
  PolyL c1 ls1 bs1 <> PolyL c2 ls2 bs2 = PolyL (c1 + c2) (ls1 <> ls2) (bs1 <> bs2)

instance (Show n, Ord n, Eq n, Num n) => Show (PolyL n) where
  show (PolyL n ls bs)
    | n == 0 =
        if firstSign == " + "
          then concat restOfTerms
          else "- " <> concat restOfTerms
    | otherwise = concat (show n : firstSign : restOfTerms)
    where
      (firstSign, restOfTerms) = case concatMap printTerm $ toList ls of
        [] -> error "[ panic ] Empty PolyG"
        (x : xs) -> (x, xs)
      -- return a pair of the sign ("+" or "-") and the string representation
      printTerm :: (Show n, Ord n, Eq n, Num n) => (Limb, n) -> [String]
      printTerm (x, c)
        | c == 0 = error "printTerm: coefficient of 0"
        | c == 1 = [" + ", show x]
        | c == -1 = [" - ", show x]
        | c < 0 = [" - ", show (Prelude.negate c) <> show x]
        | otherwise = [" + ", show c <> show x]

newL :: (Num n, Eq n) => n -> NonEmpty (Limb, n) -> PolyL n
newL c ls = PolyL c (toList ls) mempty

newB :: (Num n, Eq n) => n -> Map RefB n -> Either n (PolyL n)
newB c bs =
  if Map.null bs
    then Left c
    else Right (PolyL c mempty bs)

singletonL :: (Num n, Eq n) => n -> (Limb, n) -> Either n (PolyL n)
singletonL c (_, 0) = Left c
singletonL c (x, coeff) = Right $ PolyL c [(x, coeff)] mempty

insertL :: (Num n, Eq n) => n -> (Limb, n) -> PolyL n -> PolyL n
insertL c' x (PolyL c ls bs) = PolyL (c + c') (x : ls) bs

addConstant :: Num n => n -> PolyL n -> PolyL n
addConstant c' (PolyL c ls bs) = PolyL (c + c') ls bs

-- | Multiply all coefficients and the constant by some non-zero number
multiplyBy :: (Num n, Eq n) => n -> PolyL n -> Either n (PolyL n)
multiplyBy 0 _ = Left 0
multiplyBy m (PolyL c ls bs) = Right $ PolyL (m * c) (fmap (second (m *)) ls) (fmap (m *) bs)

view :: PolyL n -> (n, [(Limb, n)])
view (PolyL c ls bs) = (c, ls)

vars :: PolyL n -> (Set RefU, Set RefB)
vars (PolyL _ ls bs) = (Set.fromList (map (lmbRef . fst) (toList ls)), Map.keysSet bs)

limbsSet :: PolyL n -> Set Limb
limbsSet (PolyL _ ls _) = Set.fromList $ map fst (toList ls)

-- | Number of terms (including the constant)
size :: (Eq n, Num n) => PolyL n -> Int
size (PolyL c ls bs) = if c == 0 then 0 else 1 + sum (fmap (lmbWidth . fst) ls) + Map.size bs
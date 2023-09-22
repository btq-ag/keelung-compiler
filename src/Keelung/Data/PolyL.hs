{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Polynomial made of Limbs
module Keelung.Data.PolyL
  ( PolyL(polyConstant, polyLimbs, polyRefs),
    varsSet,
    limbsSet,
    newL,
    new,
    insertL,
    singletonL,
    addConstant,
    multiplyBy,
    size,
    view,
    View(..),
    viewAsRefMap
  )
where

import Control.DeepSeq (NFData)
import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
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
    -- | (Ref, coefficient)
    polyRefs :: Map Ref n
  }
  deriving (Eq, Functor, Ord, Generic, NFData)

instance (Semigroup n, Num n) => Semigroup (PolyL n) where
  PolyL c1 ls1 vars1 <> PolyL c2 ls2 vars2 = PolyL (c1 + c2) (ls1 <> ls2) (vars1 <> vars2)

instance (Show n, Ord n, Eq n, Num n) => Show (PolyL n) where
  show (PolyL n ls vars)
    | n == 0 =
        if firstSign == " + "
          then concat restOfTerms
          else "- " <> concat restOfTerms
    | otherwise = concat (show n : firstSign : toList restOfTerms)
    where
      limbTerms = mconcat $ fmap printTermL ls
      varTerms = mconcat $ fmap printTerm (Map.toList vars)

      (firstSign, restOfTerms) = case varTerms <> limbTerms of
        Seq.Empty -> error "[ panic ] Empty PolyG"
        (x Seq.:<| xs) -> (x, xs)

      -- return a pair of the sign ("+" or "-") and the string representation
      printTermL :: (Show n, Ord n, Eq n, Num n) => (Limb, n) -> Seq String
      printTermL (x, c)
        | c == 0 = error "printTerm: coefficient of 0"
        | c == 1 = Seq.fromList [" + ", show x]
        | c == -1 = Seq.fromList [" - ", show x]
        | c < 0 = Seq.fromList [" - ", show (Prelude.negate c) <> show x]
        | otherwise = Seq.fromList [" + ", show c <> show x]

      printTerm :: (Show n, Ord n, Eq n, Num n) => (Ref, n) -> Seq String
      printTerm (x, c)
        | c == 0 = error "printTerm: coefficient of 0"
        | c == 1 = Seq.fromList [" + ", show x]
        | c == -1 = Seq.fromList [" - ", show x]
        | c < 0 = Seq.fromList [" - ", show (Prelude.negate c) <> show x]
        | otherwise = Seq.fromList [" + ", show c <> show x]

newL :: (Num n, Eq n) => n -> NonEmpty (Limb, n) -> PolyL n
newL c ls = PolyL c (toList ls) mempty

new :: (Num n, Eq n) => n -> Map Ref n -> Either n (PolyL n)
new c vars =
  if Map.null vars
    then Left c
    else Right (PolyL c mempty vars)

singletonL :: (Num n, Eq n) => n -> (Limb, n) -> Either n (PolyL n)
singletonL c (_, 0) = Left c
singletonL c (x, coeff) = Right $ PolyL c [(x, coeff)] mempty

insertL :: (Num n, Eq n) => n -> (Limb, n) -> PolyL n -> PolyL n
insertL c' x (PolyL c ls vars) = PolyL (c + c') (x : ls) vars

addConstant :: Num n => n -> PolyL n -> PolyL n
addConstant c' (PolyL c ls vars) = PolyL (c + c') ls vars

-- | Multiply all coefficients and the constant by some non-zero number
multiplyBy :: (Num n, Eq n) => n -> PolyL n -> Either n (PolyL n)
multiplyBy 0 _ = Left 0
multiplyBy m (PolyL c ls vars) = Right $ PolyL (m * c) (fmap (second (m *)) ls) (fmap (m *) vars)

-- | View a PolyL as a Monomial, Binomial, or Polynomial
data View n
  = RefMonomial n (Ref, n)
  | RefBinomial n (Ref, n) (Ref, n)
  | RefPolynomial n (Map Ref n)
  | LimbMonomial n (Limb, n)
  | LimbBinomial n (Limb, n) (Limb, n)
  | LimbPolynomial n [(Limb, n)]
  | MixedPolynomial n (Map Ref n) [(Limb, n)]
  deriving (Eq, Show)

-- | View a PolyL as a Monomial, Binomial, or Polynomial
view :: PolyL n -> View n
view (PolyL constant limbs vars) =
  case (Map.toList vars, limbs) of
    ([], []) -> error "[ panic ] Empty PolyL"
    ([], [term]) -> LimbMonomial constant term
    ([], [term1, term2]) -> LimbBinomial constant term1 term2
    ([] , _) -> LimbPolynomial constant limbs
    ([term], []) -> RefMonomial constant term
    ([term1, term2], []) -> RefBinomial constant term1 term2
    (_, []) -> RefPolynomial constant vars
    _ -> MixedPolynomial constant vars limbs

-- | Convert all Limbs to Refs and return a map of Refs to coefficients
viewAsRefMap :: PolyL n -> (n, Map Ref n)
viewAsRefMap (PolyL constant limbs vars) = (constant, vars <> Map.fromList (limbs >>= limbToTerms))
  where
    limbToTerms :: (Limb, n) -> [(Ref, n)]
    limbToTerms (limb, n) = [(B (RefUBit (lmbWidth limb) (lmbRef limb) i), n) | i <- [0 .. lmbWidth limb - 1]]

varsSet :: PolyL n -> (Set RefU, Set Ref)
varsSet (PolyL _ ls vars) = (Set.fromList (map (lmbRef . fst) (toList ls)), Map.keysSet vars)

limbsSet :: PolyL n -> Set Limb
limbsSet (PolyL _ ls _) = Set.fromList $ map fst (toList ls)

-- | Number of terms (including the constant)
size :: (Eq n, Num n) => PolyL n -> Int
size (PolyL c ls vars) = if c == 0 then 0 else 1 + sum (fmap (lmbWidth . fst) ls) + Map.size vars
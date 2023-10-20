{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Polynomial made of Limbs
module Keelung.Data.PolyL
  ( PolyL (polyConstant, polyLimbs, polyRefs),
    varsSet,
    fromLimbs,
    -- fromPolyG,
    fromRefs,
    insertLimbs,
    insertRefs,
    addConstant,
    multiplyBy,
    size,
    view,
    View (..),
    viewAsRefMap,
    merge,
    negate,
  )
where

import Control.DeepSeq (NFData)
import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (Foldable (..), toList)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung.Data.Limb (Limb (..))
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference
import Prelude hiding (negate, null)
import Prelude qualified

-- | Polynomial made of Limbs + a constant
data PolyL n = PolyL
  { -- | constant term
    polyConstant :: n,
    -- | (Limb, multiplier)
    polyLimbs :: Seq (Limb, n),
    -- | (Ref, coefficient)
    polyRefs :: Map Ref n
  }
  deriving (Eq, Functor, Ord, Generic, NFData)

instance (Semigroup n, Num n) => Semigroup (PolyL n) where
  PolyL c1 ls1 vars1 <> PolyL c2 ls2 vars2 = PolyL (c1 + c2) (ls1 <> ls2) (vars1 <> vars2)

instance (Eq n, Num n, Ord n, Show n) => Show (PolyL n) where
  show (PolyL constant limbs vars)
    | constant == 0 =
        if firstSign == " + "
          then concat restOfTerms
          else "- " <> concat restOfTerms
    | otherwise = concat (show constant : firstSign : toList restOfTerms)
    where
      limbTerms = mconcat $ fmap printLimb (toList limbs)
      varTerms = mconcat $ fmap printTerm (Map.toList vars)
      (firstSign, restOfTerms) = case varTerms <> limbTerms of
        Seq.Empty -> error "[ panic ] Empty PolyL"
        (x Seq.:<| xs) -> (x, xs)

      -- return a pair of the sign ("+" or "-") and the string representation
      printLimb :: (Eq n, Num n, Ord n, Show n) => (Limb, n) -> Seq String
      printLimb (x, c) =
        let (sign, terms) = Limb.showAsTerms x
         in case c of
              0 -> error "[ panic ] PolyL: coefficient of 0"
              1 -> Seq.fromList [if sign then " + " else " - ", terms]
              -1 -> Seq.fromList [if sign then " - " else " + ", terms]
              _ -> Seq.fromList [if sign then " + " else " - ", show c <> terms]

      printTerm :: (Eq n, Num n, Ord n, Show n) => (Ref, n) -> Seq String
      printTerm (x, c)
        | c == 0 = error "printTerm: coefficient of 0"
        | c == 1 = Seq.fromList [" + ", show x]
        | c == -1 = Seq.fromList [" - ", show x]
        | c < 0 = Seq.fromList [" - ", show (Prelude.negate c) <> show x]
        | otherwise = Seq.fromList [" + ", show c <> show x]

fromLimbs :: (Num n, Eq n) => n -> [(Limb, n)] -> Either n (PolyL n)
fromLimbs constant limbs =
  let limbs' = filter ((/= 0) . snd) limbs
   in if null limbs'
        then Left constant
        else Right (PolyL constant (Seq.fromList limbs') mempty)

-- fromPolyG :: (Num n, Eq n) => PolyG n -> PolyL n
-- fromPolyG poly = let (constant, vars) = PolyG.viewAsMap poly in PolyL constant mempty vars

-- | Build a PolyL from a constant and a list of (Ref, coefficient) pairs
fromRefs :: (Num n, Eq n) => n -> [(Ref, n)] -> Either n (PolyL n)
fromRefs constant xs =
  let xs' = filter ((/= 0) . snd) xs
   in if null xs'
        then Left constant
        else Right (PolyL constant mempty (Map.fromList xs'))

insertLimbs :: (Num n, Eq n) => n -> [(Limb, n)] -> PolyL n -> PolyL n
insertLimbs c' limbs (PolyL c ls vars) = PolyL (c + c') (Seq.fromList limbs <> ls) vars

insertRefs :: (Num n, Eq n) => n -> [(Ref, n)] -> PolyL n -> Either n (PolyL n)
insertRefs c' xs (PolyL c limbs vars) =
  let vars' = cleanVars $ Map.unionWith (+) vars (Map.fromList xs)
   in if Seq.null limbs && Map.null vars'
        then Left c
        else Right $ PolyL (c + c') limbs vars'

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
  case (Map.toList vars, toList limbs) of
    ([], []) -> error "[ panic ] Empty PolyL"
    ([], [term]) -> LimbMonomial constant term
    ([], [term1, term2]) -> LimbBinomial constant term1 term2
    ([], _) -> LimbPolynomial constant (toList limbs)
    ([term], []) -> RefMonomial constant term
    ([term1, term2], []) -> RefBinomial constant term1 term2
    (_, []) -> RefPolynomial constant vars
    _ -> MixedPolynomial constant vars (toList limbs)

-- | Convert all Limbs to Refs and return a map of Refs to coefficients
viewAsRefMap :: PolyL n -> (n, Map Ref n)
viewAsRefMap (PolyL constant limbs vars) = (constant, vars <> Map.fromList (toList limbs >>= limbToTerms))
  where
    limbToTerms :: (Limb, n) -> [(Ref, n)]
    limbToTerms (limb, n) = [(B (RefUBit (lmbWidth limb) (lmbRef limb) i), n) | i <- [0 .. lmbWidth limb - 1]]

-- | Return a set of all Refs in the PolyL
varsSet :: PolyL n -> (Set RefU, Set Ref)
varsSet (PolyL _ ls vars) = (Set.fromList (map (lmbRef . fst) (toList ls)), Map.keysSet vars)

-- | Number of terms (including the constant)
size :: (Eq n, Num n) => PolyL n -> Int
size (PolyL c ls vars) = (if c == 0 then 0 else 1) + sum (fmap (lmbWidth . fst) ls) + Map.size vars

-- | Merge two PolyLs
merge :: (Num n, Eq n) => PolyL n -> PolyL n -> Either n (PolyL n)
merge (PolyL c1 ls1 vars1) (PolyL c2 ls2 vars2) =
  let limbs = ls1 <> ls2
      vars = cleanVars $ Map.unionWith (+) vars1 vars2
   in if null limbs && Map.null vars
        then Left (c1 + c2)
        else Right (PolyL (c1 + c2) limbs vars)

-- | Negate a polynomial
negate :: (Num n, Eq n) => PolyL n -> PolyL n
negate (PolyL c ls vars) = PolyL (-c) (fmap (second Prelude.negate) ls) (fmap Prelude.negate vars)

--------------------------------------------------------------------------------

-- | Helper function for cleaning a Map of Refs
cleanVars :: (Num n, Eq n) => Map Ref n -> Map Ref n
cleanVars = Map.filter (/= 0)
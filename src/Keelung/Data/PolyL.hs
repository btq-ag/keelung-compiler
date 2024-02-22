{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Polynomial made of References and Slices
module Keelung.Data.PolyL
  ( -- * Eliminators
    PolyL (polyConstant, polyLimbs, polyRefs),
    new,

    -- * Constructors
    fromLimbs,
    fromLimb,
    fromRefs,

    -- * Operations
    insertLimbs,
    insertRefs,
    addConstant,
    multiplyBy,
    merge,
    negate,

    -- * Predicates
    view,
    View (..),
    size,
    isValid,
  )
where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (..), toList)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import GHC.Generics (Generic)
import Keelung (widthOf)
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
    polyLimbs :: Map Limb n,
    -- | (Ref, coefficient)
    polyRefs :: Map Ref n,
    -- | (Slice, coefficient)
    polySlices :: Map Ref n
  }
  deriving (Eq, Functor, Ord, Generic, NFData)

instance (Integral n, GaloisField n) => Show (PolyL n) where
  show (PolyL constant limbs refs _)
    | constant == 0 =
        if firstSign == " + "
          then concat restOfTerms
          else "- " <> concat restOfTerms
    | otherwise = concat (show constant : firstSign : toList restOfTerms)
    where
      limbTerms = mconcat $ fmap printLimb (Map.toList limbs)
      varTerms = mconcat $ fmap printTerm (Map.toList refs)
      (firstSign, restOfTerms) = case varTerms <> limbTerms of
        Seq.Empty -> error "[ panic ] Empty PolyL"
        (x Seq.:<| xs) -> (x, xs)

      -- return a pair of the sign ("+" or "-") and the string representation
      printLimb :: (Integral n, GaloisField n) => (Limb, n) -> Seq String
      printLimb (x, c) =
        let (sign, terms) = Limb.showAsTerms x
         in case c of
              0 -> error "[ panic ] PolyL: coefficient of 0"
              1 -> Seq.fromList [if sign then " + " else " - ", terms]
              -1 -> Seq.fromList [if sign then " - " else " + ", terms]
              _ -> Seq.fromList [if sign then " + " else " - ", show c <> terms]

      printTerm :: (Integral n, GaloisField n) => (Ref, n) -> Seq String
      printTerm (x, c)
        | c == 0 = error "printTerm: coefficient of 0"
        | c == 1 = Seq.fromList [" + ", show x]
        | c == -1 = Seq.fromList [" - ", show x]
        | c < 0 = Seq.fromList [" - ", show (Prelude.negate c) <> show x]
        | otherwise = Seq.fromList [" + ", show c <> show x]

--------------------------------------------------------------------------------

-- | Construct a PolyL from a constant, Refs, and Limbs
new :: (Integral n) => n -> [(Ref, n)] -> [(Limb, n)] -> Either n (PolyL n)
new constant refs limbs = case (toMap refs, toMap limbs) of
  (Nothing, Nothing) -> Left constant
  (Nothing, Just limbs') -> Right (PolyL constant limbs' mempty mempty)
  (Just refs', Nothing) -> Right (PolyL constant mempty refs' mempty)
  (Just refs', Just limbs') -> Right (PolyL constant limbs' refs' mempty)

-- | Construct a PolyL from a constant and a list of (Limb, coefficient) pairs
fromLimbs :: (Integral n) => n -> [(Limb, n)] -> Either n (PolyL n)
fromLimbs constant xs =
  case toMap xs of
    Nothing -> Left constant
    Just limbs -> Right (PolyL constant limbs mempty mempty)

-- | Construct a PolyL from a constant and a single Limb
fromLimb :: (Integral n) => n -> Limb -> PolyL n
fromLimb constant limb = PolyL constant (Map.singleton limb 1) mempty mempty

-- | Construct a PolyL from a constant and a list of (Ref, coefficient) pairs
fromRefs :: (Integral n) => n -> [(Ref, n)] -> Either n (PolyL n)
fromRefs constant xs = case toMap xs of
  Nothing -> Left constant
  Just refs -> Right (PolyL constant mempty refs mempty)

--------------------------------------------------------------------------------

-- | Insert a list of (Limb, coefficient) pairs into a PolyL
insertLimbs :: (Integral n) => n -> [(Limb, n)] -> PolyL n -> Either n (PolyL n)
insertLimbs c' ls' (PolyL c ls rs ss) =
  let limbs = mergeListAndClean ls ls'
   in if null limbs && null rs
        then Left (c + c')
        else Right (PolyL (c + c') limbs rs ss)

insertRefs :: (Integral n) => n -> [(Ref, n)] -> PolyL n -> Either n (PolyL n)
insertRefs c' rs' (PolyL c ls rs ss) =
  let refs = mergeListAndClean rs rs'
   in if null rs' && null ls
        then Left (c + c')
        else Right $ PolyL (c + c') ls refs ss

addConstant :: (Integral n) => n -> PolyL n -> PolyL n
addConstant c' (PolyL c ls rs ss) = PolyL (c + c') ls rs ss

-- | Multiply all coefficients and the constant by some non-zero number
multiplyBy :: (Integral n) => n -> PolyL n -> Either n (PolyL n)
multiplyBy 0 _ = Left 0
multiplyBy m (PolyL c ls rs ss) = Right $ PolyL (m * c) (fmap (m *) ls) (fmap (m *) rs) (fmap (m *) ss)

-- | Merge two PolyLs
merge :: (Integral n) => PolyL n -> PolyL n -> Either n (PolyL n)
merge (PolyL c1 ls1 rs1 ss1) (PolyL c2 ls2 rs2 ss2) =
  let limbs = mergeAndClean ls1 ls2
      refs = mergeAndClean rs1 rs2
      slices = mergeAndClean ss1 ss2
   in if null limbs && null refs
        then Left (c1 + c2)
        else Right (PolyL (c1 + c2) limbs refs slices)

-- | Negate a polynomial
negate :: (Num n, Eq n) => PolyL n -> PolyL n
negate (PolyL c ls rs ss) = PolyL (-c) (fmap Prelude.negate ls) (fmap Prelude.negate rs) (fmap Prelude.negate ss)

--------------------------------------------------------------------------------

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
view (PolyL constant limbs refs _) =
  case (Map.toList refs, Map.toList limbs) of
    ([], []) -> error "[ panic ] Empty PolyL"
    ([], [term]) -> LimbMonomial constant term
    ([], [term1, term2]) -> LimbBinomial constant term1 term2
    ([], _) -> LimbPolynomial constant (Map.toList limbs)
    ([term], []) -> RefMonomial constant term
    ([term1, term2], []) -> RefBinomial constant term1 term2
    (_, []) -> RefPolynomial constant refs
    _ -> MixedPolynomial constant refs (Map.toList limbs)

-- | Number of terms (including the constant)
size :: (Eq n, Num n) => PolyL n -> Int
size (PolyL c limbs refs _) = (if c == 0 then 0 else 1) + sum (fmap lmbWidth (Map.keys limbs)) + Map.size refs

--------------------------------------------------------------------------------

-- | See if a PolyL is valid
isValid :: (Integral n) => PolyL n -> Bool
isValid (PolyL _ limbs refs _) = not (null (Map.filter (/= 0) limbs)) || not (Map.null (Map.filter (/= 0) refs)) && all ((> 0) . widthOf) (Map.keys limbs)

-- | Helper function for converting a list of (a, n) pairs to a Map
toMap :: (Integral n, Ord a) => [(a, n)] -> Maybe (Map a n)
toMap xs =
  let result = Map.filter (/= 0) (Map.fromListWith (+) xs)
   in if Map.null result
        then Nothing
        else Just result

mergeAndClean :: (Integral n, Ord a) => Map a n -> Map a n -> Map a n
mergeAndClean xs ys = Map.filter (/= 0) (Map.unionWith (+) xs ys)

mergeListAndClean :: (Integral n, Ord a) => Map a n -> [(a, n)] -> Map a n
mergeListAndClean xs ys = Map.filter (/= 0) (Map.unionWith (+) xs (Map.fromListWith (+) ys))
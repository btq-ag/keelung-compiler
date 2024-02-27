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
    toSlices,

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

    -- * Testing
    Error (..),
    validate,
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
import Keelung.Data.IntervalSet (IntervalSet)
import Keelung.Data.IntervalSet qualified as IntervalSet
import Keelung.Data.Limb (Limb (..))
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
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
    polySlices :: Map RefU (IntervalSet n)
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
new :: (Integral n) => n -> [(Ref, n)] -> [(Slice, n)] -> Either n (PolyL n)
new constant refs slices = case (toMap refs, fromSlices slices) of
  (Nothing, Nothing) -> Left constant
  (Nothing, Just slices') -> Right (PolyL constant mempty mempty slices')
  (Just refs', Nothing) -> Right (PolyL constant mempty refs' mempty)
  (Just refs', Just slices') -> Right (PolyL constant mempty refs' slices')

-- | Construct a PolyL from a constant and a list of (Limb, coefficient) pairs
fromLimbs :: (Integral n) => n -> [(Limb, n)] -> Either n (PolyL n)
fromLimbs constant xs =
  case (toMap xs, toIntervalSets xs) of
    (Nothing, Nothing) -> Left constant
    (Nothing, Just _) -> error "[ panic ] PolyL.fromLimbs: impossible"
    (Just _, Nothing) -> error "[ panic ] PolyL.fromLimbs: impossible"
    (Just limbs, Just slices) -> Right (PolyL constant limbs mempty slices)

-- | Convert a PolyL to a list of (Slice, coefficient) pairs
toSlices :: PolyL n -> [(Slice, n)]
toSlices = concatMap (uncurry IntervalSet.toSlices) . Map.toList . polySlices

-- | Construct a PolyL from a constant and a single Limb
fromLimb :: (Integral n) => n -> Limb -> PolyL n
fromLimb constant limb = PolyL constant (Map.singleton limb 1) mempty (Map.singleton (lmbRef limb) (IntervalSet.fromLimb (limb, 1)))

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
      slices = case toIntervalSets ls' of
        Nothing -> ss
        Just ss' -> mergeIntervalSetAndClean ss ss'
   in if null limbs && null rs
        then Left (c + c')
        else Right (PolyL (c + c') limbs rs slices)

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
multiplyBy m (PolyL c ls rs ss) = Right $ PolyL (m * c) (fmap (m *) ls) (fmap (m *) rs) (fmap (fmap (m *)) ss)

-- | Merge two PolyLs
merge :: (Integral n) => PolyL n -> PolyL n -> Either n (PolyL n)
merge (PolyL c1 ls1 rs1 ss1) (PolyL c2 ls2 rs2 ss2) =
  let limbs = mergeAndClean ls1 ls2
      refs = mergeAndClean rs1 rs2
      slices = mergeIntervalSetAndClean ss1 ss2
   in if null limbs && null refs
        then Left (c1 + c2)
        else Right (PolyL (c1 + c2) limbs refs slices)

-- | Negate a polynomial
negate :: (Num n, Eq n) => PolyL n -> PolyL n
negate (PolyL c ls rs ss) = PolyL (-c) (fmap Prelude.negate ls) (fmap Prelude.negate rs) (fmap (fmap Prelude.negate) ss)

--------------------------------------------------------------------------------

-- | View a PolyL as a Monomial, Binomial, or Polynomial
data View n
  = RefMonomial n (Ref, n)
  | RefBinomial n (Ref, n) (Ref, n)
  | RefPolynomial n (Map Ref n)
  | SliceMonomial n (Slice, n)
  | SliceBinomial n (Slice, n) (Slice, n)
  | SlicePolynomial n [(Slice, n)]
  | MixedPolynomial n (Map Ref n) [(Slice, n)]
  deriving (Eq, Show)

-- | View a PolyL as a Monomial, Binomial, or Polynomial
view :: PolyL n -> View n
view (PolyL constant _ refs intervals) =
  let slices = toSlices_ intervals
   in case (Map.toList refs, slices) of
        ([], [slice]) -> SliceMonomial constant slice
        ([], []) -> error "[ panic ] PolyL.view: empty"
        ([], [slice1, slice2]) -> SliceBinomial constant slice1 slice2
        ([], _) -> SlicePolynomial constant slices
        ([term], []) -> RefMonomial constant term
        ([term1, term2], []) -> RefBinomial constant term1 term2
        (_, []) -> RefPolynomial constant refs
        _ -> MixedPolynomial constant refs slices

-- | Number of terms (including the constant)
size :: (Eq n, Num n) => PolyL n -> Int
size (PolyL c _ refs intervals) = (if c == 0 then 0 else 1) + Map.size refs + length (concatMap (uncurry IntervalSet.toSlices) (Map.toList intervals))

--------------------------------------------------------------------------------

data Error n
  = ConstantOnly -- The polynomial does not have any non-contant terms
  | LimbsWithZeroWidth [Limb] -- The polynomial has Limbs with zero width
  | InvalidSlices [IntervalSet.Error n] -- The polynomial has invalid Slices
  deriving (Eq, Show)

-- | Validate a PolyL
validate :: (Integral n) => PolyL n -> Maybe (Error n)
validate (PolyL _ limbs refs slices) =
  let limbsNonZero = not (Map.null (Map.filter (/= 0) limbs))
      refsNonZero = not (Map.null (Map.filter (/= 0) refs))
      slicesNonZero = not (Map.null (Map.filter (not . IntervalSet.allZero) slices))
      notConstantOnly = limbsNonZero || refsNonZero || slicesNonZero
      limbsWithZeroWidth = filter ((== 0) . widthOf) (Map.keys limbs)
      invalidSlices = toList $ Map.mapMaybe IntervalSet.validate slices
   in -- invalidSlices = map fst $ toSlices $ Map.filter (not . IntervalSet.isValid) slices
      if notConstantOnly
        then
          if null limbsWithZeroWidth
            then
              if null invalidSlices
                then Nothing
                else Just (InvalidSlices invalidSlices)
            else Just (LimbsWithZeroWidth limbsWithZeroWidth)
        else Just ConstantOnly

-- | Helper function for converting a list of (a, n) pairs to a Map
toMap :: (Integral n, Ord a) => [(a, n)] -> Maybe (Map a n)
toMap xs =
  let result = Map.filter (/= 0) (Map.fromListWith (+) xs)
   in if Map.null result
        then Nothing
        else Just result

-- | From a list of (Limb, n) pairs to a Map of IntervalSets
toIntervalSets :: (Integral n) => [(Limb, n)] -> Maybe (Map RefU (IntervalSet n))
toIntervalSets pairs =
  let fromPair (limb, n) = (lmbRef limb, IntervalSet.fromLimb (limb, n))
      xs = Map.fromListWith (<>) (map fromPair pairs)
      result = Map.filter (not . IntervalSet.allZero) xs
   in if Map.null result
        then Nothing
        else Just result

toSlices_ :: Map RefU (IntervalSet n) -> [(Slice, n)]
toSlices_ = concatMap (uncurry IntervalSet.toSlices) . Map.toList

-- | From a list of (Slice, n) pairs to a Map of valid IntervalSets
fromSlices :: (Num n, Eq n) => [(Slice, n)] -> Maybe (Map RefU (IntervalSet n))
fromSlices pairs =
  let raw = Map.mapMaybe id $ Map.fromListWith mergeEntry (map (\(slice, n) -> (Slice.sliceRefU slice, IntervalSet.fromSlice (slice, n))) pairs)
      result = Map.filter (not . IntervalSet.allZero) raw
   in if Map.null result
        then Nothing
        else Just result
  where
    mergeEntry Nothing xs = xs
    mergeEntry xs Nothing = xs
    mergeEntry (Just xs) (Just ys) = Just (xs <> ys)

mergeAndClean :: (Integral n, Ord a) => Map a n -> Map a n -> Map a n
mergeAndClean xs ys = Map.filter (/= 0) (Map.unionWith (+) xs ys)

mergeIntervalSetAndClean :: (Integral n, Ord a) => Map a (IntervalSet n) -> Map a (IntervalSet n) -> Map a (IntervalSet n)
mergeIntervalSetAndClean xs ys = Map.filter (not . IntervalSet.allZero) (Map.unionWith (<>) xs ys)

mergeListAndClean :: (Integral n, Ord a) => Map a n -> [(a, n)] -> Map a n
mergeListAndClean xs ys = Map.filter (/= 0) (Map.unionWith (+) xs (Map.fromListWith (+) ys))
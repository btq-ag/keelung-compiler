{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Polynomial made of References and Slices
module Keelung.Data.PolyL
  ( -- * Eliminators
    PolyL (polyConstant, polyLimbs, polyRefs),
    new,

    -- * Constructors
    fromLimbs,
    fromRef,
    fromRefs,
    fromSlice,
    toSlices,
    sliceToLimb,

    -- * Operations
    insertSlices,
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
import Data.Bifunctor (first)
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (..), toList)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe qualified
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
import Keelung.Data.SlicePolynomial (SlicePoly)
import Keelung.Data.SlicePolynomial qualified as SlicePoly
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
    polySlices :: Map RefU (IntervalSet n),
    -- | SlicePolynomial
    polySlices2 :: SlicePoly n
  }
  deriving (Eq, Functor, Ord, Generic)

instance (NFData n) => NFData (PolyL n)

instance (Integral n, GaloisField n) => Show (PolyL n) where
  show (PolyL constant limbs refs _ slicePolys)
    | constant == 0 =
        if firstSign == " + "
          then concat restOfTerms
          else "- " <> concat restOfTerms
    | otherwise = concat (show constant : firstSign : toList restOfTerms)
    where
      limbTerms = mconcat $ fmap printLimb (Map.toList limbs)
      refTerms = mconcat $ fmap printRefs (Map.toList refs)
      slices = SlicePoly.toSlices slicePolys
      sliceTerms = mconcat $ fmap printSlice slices

      (firstSign, restOfTerms) = case refTerms <> limbTerms <> sliceTerms of
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

      printSlice :: (Integral n, GaloisField n) => (Slice, n) -> Seq String
      printSlice (x, c)
        | c == 0 = error "printSlice: coefficient of 0"
        | c == 1 = Seq.fromList [" + ", show x]
        | c == -1 = Seq.fromList [" - ", show x]
        | c < 0 = Seq.fromList [" - ", show (Prelude.negate c) <> show x]
        | otherwise = Seq.fromList [" + ", show c <> show x]

      printRefs :: (Integral n, GaloisField n) => (Ref, n) -> Seq String
      printRefs (x, c)
        | c == 0 = error "printRefs: coefficient of 0"
        | c == 1 = Seq.fromList [" + ", show x]
        | c == -1 = Seq.fromList [" - ", show x]
        | c < 0 = Seq.fromList [" - ", show (Prelude.negate c) <> show x]
        | otherwise = Seq.fromList [" + ", show c <> show x]

--------------------------------------------------------------------------------

-- | Construct a PolyL from a constant, Refs, and Limbs
new :: (Integral n, GaloisField n) => n -> [(Ref, n)] -> [(Slice, n)] -> Either n (PolyL n)
new constant refs slices =
  case (toRefMap refs, fromSlicesHelper slices) of
    (Nothing, Nothing) -> Left constant
    (Nothing, Just (limbs', slices', slices2')) -> Right (PolyL constant limbs' mempty slices' slices2')
    (Just refs', Nothing) -> Right (PolyL constant mempty refs' mempty mempty)
    (Just refs', Just (limbs', slices', slices2')) -> Right (PolyL constant limbs' refs' slices' slices2')

-- | Helper for converting Slices to Limbs and make sure they are equal
fromSlicesHelper :: (Integral n, GaloisField n) => [(Slice, n)] -> Maybe (Map Limb n, Map RefU (IntervalSet n), SlicePoly n)
fromSlicesHelper slices =
  let slicePoly = slicesToIntervalMap slices
   in case toLimbMap (fmap (first sliceToLimb) slices) of
        Nothing ->
          if null slicePoly
            then Just (mempty, mempty, mempty)
            else error "[ panic ] PolyL.fromSlicesHelper: empty Limbs with non-empty Slices"
        Just limbs ->
          if limbsToIntervalMap (Map.toList limbs) == slicePoly
            then Just (limbs, slicePoly, SlicePoly.fromSlices slices)
            else error $ "[ panic ] PolyL.fromSlicesHelper: mismatch between Slices & Limbs:\n  Slices: " <> show (map fst slices) <> "\n  Limbs: " <> show (Map.keys limbs)

-- | Helper for converting Limbs to Slices and make sure they are equal
fromLimbsHelper :: (Integral n, GaloisField n) => [(Limb, n)] -> Maybe (Map Limb n, Map RefU (IntervalSet n), SlicePoly n)
fromLimbsHelper xs =
  let intervalMap = limbsToIntervalMap xs
   in case toLimbMap xs of
        Nothing ->
          if null intervalMap
            then Nothing
            else error $ "[ panic ] PolyL.fromLimbsHelper: empty Limbs with non-empty Slices:\n  Slices: " <> show (map fst $ intervalMaptoSlices intervalMap)
        Just limbs -> Just (limbs, intervalMap, SlicePoly.fromSlices (intervalMaptoSlices intervalMap))

-- | Construct a PolyL from a single Ref
fromRef :: (Integral n, GaloisField n) => Ref -> PolyL n
fromRef ref = PolyL 0 mempty (Map.singleton ref 1) mempty mempty

-- | Construct a PolyL from a constant and a list of (Limb, coefficient) pairs
fromLimbs :: (Integral n, GaloisField n) => n -> [(Limb, n)] -> Either n (PolyL n)
fromLimbs constant xs = case fromLimbsHelper xs of
  Nothing -> Left constant
  Just (limbs, slices, slices2) -> Right (PolyL constant limbs mempty slices slices2)

-- | Convert a PolyL to a list of (Slice, coefficient) pairs
toSlices :: PolyL n -> [(Slice, n)]
toSlices = concatMap (uncurry IntervalSet.toSlices) . Map.toList . polySlices

-- | Construct a PolyL from a constant and a single slice
fromSlice :: (Integral n, GaloisField n) => n -> Slice -> PolyL n
fromSlice constant slice = PolyL constant (Map.singleton (sliceToLimb slice) 1) mempty (slicesToIntervalMap [(slice, 1)]) (SlicePoly.fromSlices [(slice, 1)])

-- | Construct a PolyL from a constant and a list of (Ref, coefficient) pairs
fromRefs :: (Integral n, GaloisField n) => n -> [(Ref, n)] -> Either n (PolyL n)
fromRefs constant xs = case toRefMap xs of
  Nothing -> Left constant
  Just refs -> Right (PolyL constant mempty refs mempty mempty)

--------------------------------------------------------------------------------

-- | Insert a list of (Slice, coefficient) pairs into a PolyL
insertSlices :: (Integral n, GaloisField n) => [(Slice, n)] -> PolyL n -> Either n (PolyL n)
insertSlices ss' (PolyL c ls rs ss ss2) =
  let limbs = mergeAndClean ls (Data.Maybe.fromMaybe mempty (toLimbMap (fmap (first sliceToLimb) ss')))
      slices = mergeIntervalSetAndClean ss (slicesToIntervalMap ss')
   in Right (PolyL c limbs rs slices (SlicePoly.insertMany ss' ss2))

insertRefs :: (Integral n) => n -> [(Ref, n)] -> PolyL n -> Either n (PolyL n)
insertRefs c' rs' (PolyL c ls rs ss ss2) =
  let refs = mergeListAndClean rs rs'
   in if null rs' && null ls
        then Left (c + c')
        else Right $ PolyL (c + c') ls refs ss ss2

addConstant :: (Integral n) => n -> PolyL n -> PolyL n
addConstant c' (PolyL c ls rs ss ss2) = PolyL (c + c') ls rs ss ss2

-- | Multiply all coefficients and the constant by some non-zero number
multiplyBy :: (Integral n, GaloisField n) => n -> PolyL n -> Either n (PolyL n)
multiplyBy 0 _ = Left 0
multiplyBy m (PolyL c ls rs ss ss2) = Right $ PolyL (m * c) (fmap (m *) ls) (fmap (m *) rs) (fmap (fmap (m *)) ss) (SlicePoly.multiplyBy m ss2)

-- | Merge two PolyLs
merge :: (Integral n, GaloisField n) => PolyL n -> PolyL n -> Either n (PolyL n)
merge (PolyL c1 ls1 rs1 ss1 sp1) (PolyL c2 ls2 rs2 ss2 sp2) =
  let limbs = mergeAndClean ls1 ls2
      refs = mergeAndClean rs1 rs2
      slices = mergeIntervalSetAndClean ss1 ss2
   in if null limbs && null refs
        then Left (c1 + c2)
        else Right (PolyL (c1 + c2) limbs refs slices (sp1 <> sp2))

-- | Negate a polynomial
negate :: (Integral n, GaloisField n) => PolyL n -> PolyL n
negate (PolyL c ls rs ss sp) = PolyL (-c) (fmap Prelude.negate ls) (fmap Prelude.negate rs) (fmap (fmap Prelude.negate) ss) (SlicePoly.multiplyBy (-1) sp)

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
view (PolyL constant _ refs intervals _) =
  let slices = intervalMaptoSlices intervals
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
size (PolyL c _ refs intervals _) = (if c == 0 then 0 else 1) + Map.size refs + length (concatMap (uncurry IntervalSet.toSlices) (Map.toList intervals))

--------------------------------------------------------------------------------

data Error n
  = ConstantOnly -- The polynomial does not have any non-contant terms
  | LimbsWithZeroWidth [Limb] -- The polynomial has Limbs with zero width
  | InvalidSlices [IntervalSet.Error n] -- The polynomial has invalid Slices
  | LimbsNotConsistentWithSlices (n, Map RefU (IntervalSet n)) (n, Map Limb n)
  deriving (Eq, Show)

-- | Validate a PolyL
validate :: (Integral n) => PolyL n -> Maybe (Error n)
validate (PolyL _ limbs refs slices _) =
  let limbsNonZero = not (Map.null (Map.filter (/= 0) limbs))
      refsNonZero = not (Map.null (Map.filter (/= 0) refs))
      slicesNonZero = not (Map.null (Map.filter (not . IntervalSet.allZero) slices))
      notConstantOnly = limbsNonZero || refsNonZero || slicesNonZero
      limbsWithZeroWidth = filter ((== 0) . widthOf) (Map.keys limbs)
      invalidSlices = toList $ Map.mapMaybe IntervalSet.validate slices
   in if notConstantOnly
        then
          if null limbsWithZeroWidth
            then
              if null invalidSlices
                then
                  if consistentLimbsAndSlices
                    then Nothing
                    else Just (LimbsNotConsistentWithSlices (sliceCoeffSum, slices) (limbCoeffSum, limbs))
                else Just (InvalidSlices invalidSlices)
            else Just (LimbsWithZeroWidth limbsWithZeroWidth)
        else Just ConstantOnly
  where
    -- we consider a set of Limbs and a set of Slices to be consistent,
    --   if the sum of their coefficients are equal to each other
    consistentLimbsAndSlices :: Bool
    consistentLimbsAndSlices = limbCoeffSum == sliceCoeffSum
    limbCoeffSum = sum $ Map.mapWithKey (\limb n -> fromIntegral (widthOf limb) * n) limbs
    sliceCoeffSum = sum (fmap IntervalSet.totalCount slices)

toRefMap :: (Integral n) => [(Ref, n)] -> Maybe (Map Ref n)
toRefMap xs =
  let result = Map.filter (/= 0) (Map.fromListWith (+) xs)
   in if Map.null result
        then Nothing
        else Just result

toLimbMap :: (Integral n) => [(Limb, n)] -> Maybe (Map Limb n)
toLimbMap xs =
  let result = Map.filterWithKey (\limb n -> not (Limb.null limb) && n /= 0) (Map.fromListWith (+) xs)
   in if Map.null result
        then Nothing
        else Just result

-- | From a list of (Limb, n) pairs to a Map of IntervalSets
limbsToIntervalMap :: (Integral n) => [(Limb, n)] -> Map RefU (IntervalSet n)
limbsToIntervalMap pairs =
  let fromPair (limb, n) = (lmbRef limb, IntervalSet.fromLimb (limb, n))
      xs = Map.fromListWith (<>) (map fromPair pairs)
   in Map.filter (not . IntervalSet.allZero) xs

sliceToLimb :: Slice -> Limb
sliceToLimb (Slice.Slice ref start end) = Limb.new ref (end - start) start (Left True)

intervalMaptoSlices :: Map RefU (IntervalSet n) -> [(Slice, n)]
intervalMaptoSlices = concatMap (uncurry IntervalSet.toSlices) . Map.toList

-- | From a list of (Slice, n) pairs to a Map of valid IntervalSets
slicesToIntervalMap :: (Num n, Eq n) => [(Slice, n)] -> Map RefU (IntervalSet n)
slicesToIntervalMap pairs =
  Map.filter (not . IntervalSet.allZero) $ Map.mapMaybe id $ Map.fromListWith mergeEntry (map (\(slice, n) -> (Slice.sliceRefU slice, IntervalSet.fromSlice (slice, n))) pairs)
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
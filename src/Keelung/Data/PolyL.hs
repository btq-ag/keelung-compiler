{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Polynomial made of References and Slices
module Keelung.Data.PolyL
  ( -- * Eliminators
    PolyL (polyConstant, polyRefs),
    new,

    -- * Constructors
    fromLimbs,
    fromRef,
    fromRefs,
    fromSlice,
    toSlices,

    -- * Operations
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
import Keelung.Data.IntervalSet qualified as IntervalSet
import Keelung.Data.Limb (Limb)
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
    -- | (Ref, coefficient)
    polyRefs :: Map Ref n,
    -- | SlicePolynomial
    polySlices :: SlicePoly n
  }
  deriving (Eq, Functor, Ord, Generic)

instance (NFData n) => NFData (PolyL n)

instance (Integral n, GaloisField n) => Show (PolyL n) where
  show (PolyL constant refs slicePolys)
    | constant == 0 =
        if firstSign == " + "
          then concat restOfTerms
          else "- " <> concat restOfTerms
    | otherwise = concat (show constant : firstSign : toList restOfTerms)
    where
      refTerms = mconcat $ fmap printRefs (Map.toList refs)
      slices = SlicePoly.toSlices slicePolys
      sliceTerms = mconcat $ fmap printSlice slices

      (firstSign, restOfTerms) = case refTerms <> sliceTerms of
        Seq.Empty -> error "[ panic ] Empty PolyL"
        (x Seq.:<| xs) -> (x, xs)

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
-- shortcuts
new constant [] [] = Left constant
new constant [] [(_, 0)] = Left constant
new constant [] [(slice1, b1)] = Right (PolyL constant mempty (SlicePoly.fromSlices [(slice1, b1)]))
new constant [(_, 0)] [] = Left constant
new constant [(ref1, a1)] [] = Right (PolyL constant (Map.singleton ref1 a1) mempty)
new constant refs slices =
  let slices' = SlicePoly.fromSlices slices
   in if SlicePoly.null slices'
        then case toRefMap refs of
          Nothing -> Left constant
          Just refs' -> Right (PolyL constant refs' mempty)
        else case toRefMap refs of
          Nothing -> Right (PolyL constant mempty slices')
          Just refs' -> Right (PolyL constant refs' slices')

-- | Construct a PolyL from a single Ref
fromRef :: (Integral n, GaloisField n) => Ref -> PolyL n
fromRef ref = PolyL 0 (Map.singleton ref 1) mempty

-- | Construct a PolyL from a constant and a list of (Limb, coefficient) pairs
fromLimbs :: (Integral n, GaloisField n) => n -> [(Limb, n)] -> Either n (PolyL n)
fromLimbs constant xs =
  let slicePoly = limbsToSlicePoly xs
   in if SlicePoly.null slicePoly
        then Left constant
        else Right (PolyL constant mempty (limbsToSlicePoly xs))

-- | Convert a PolyL to a list of (Slice, coefficient) pairs
toSlices :: (Num n) => PolyL n -> [(Slice, n)]
toSlices = SlicePoly.toSlices . polySlices

-- | Construct a PolyL from a constant and a single slice
fromSlice :: (Integral n, GaloisField n) => n -> Slice -> PolyL n
fromSlice constant slice = PolyL constant mempty (SlicePoly.fromSlices [(slice, 1)])

-- | Construct a PolyL from a constant and a list of (Ref, coefficient) pairs
fromRefs :: (Integral n, GaloisField n) => n -> [(Ref, n)] -> Either n (PolyL n)
fromRefs constant xs = case toRefMap xs of
  Nothing -> Left constant
  Just refs -> Right (PolyL constant refs mempty)

--------------------------------------------------------------------------------

-- | Add a constant to a PolyL
addConstant :: (Integral n) => n -> PolyL n -> PolyL n
addConstant c' (PolyL c rs ss) = PolyL (c + c') rs ss

-- | Multiply all coefficients and the constant by some non-zero number
multiplyBy :: (Integral n, GaloisField n) => n -> PolyL n -> Either n (PolyL n)
multiplyBy 0 _ = Left 0
multiplyBy m (PolyL c rs ss) = Right $ PolyL (m * c) (fmap (m *) rs) (SlicePoly.multiplyBy m ss)

-- | Merge two PolyLs
merge :: (Integral n, GaloisField n) => PolyL n -> PolyL n -> Either n (PolyL n)
merge (PolyL c1 rs1 sp1) (PolyL c2 rs2 sp2) =
  let refs = mergeRefsAndClean rs1 rs2
      slicePoly = sp1 <> sp2
   in if null refs && SlicePoly.null slicePoly
        then Left (c1 + c2)
        else Right (PolyL (c1 + c2) refs (sp1 <> sp2))

-- | Negate a polynomial
negate :: (Integral n, GaloisField n) => PolyL n -> PolyL n
negate (PolyL c rs sp) = PolyL (-c) (fmap Prelude.negate rs) (SlicePoly.multiplyBy (-1) sp)

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
view :: (Num n) => PolyL n -> View n
view (PolyL constant refs slicePoly) =
  let slices = SlicePoly.toSlices slicePoly
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
size :: (Integral n) => PolyL n -> Int
size (PolyL c refs slicePoly) = (if c == 0 then 0 else 1) + Map.size refs + SlicePoly.size slicePoly

--------------------------------------------------------------------------------

data Error n
  = ConstantOnly -- The polynomial does not have any non-contant terms
  | InvalidSlices [(RefU, IntervalSet.Error n)] -- The polynomial has invalid Slices
  deriving (Eq, Show)

-- | Validate a PolyL
validate :: (Integral n) => PolyL n -> Maybe (Error n)
validate (PolyL _ refs slicePoly) =
  let refsNonZero = not (Map.null (Map.filter (/= 0) refs))
      slicesNonZero = not (SlicePoly.null slicePoly)
      notConstantOnly = refsNonZero || slicesNonZero
      invalidSlices = SlicePoly.validate slicePoly
   in if notConstantOnly
        then
          if null invalidSlices
            then Nothing
            else Just (InvalidSlices invalidSlices)
        else Just ConstantOnly

toRefMap :: (Integral n) => [(Ref, n)] -> Maybe (Map Ref n)
toRefMap xs =
  let result = Map.filter (/= 0) (Map.fromListWith (+) xs)
   in if Map.null result
        then Nothing
        else Just result

limbsToSlicePoly :: (Integral n, GaloisField n) => [(Limb, n)] -> SlicePoly n
limbsToSlicePoly =
  SlicePoly.fromSlices
    . concatMap
      ( \(limb, n) ->
          [(slice, n * fromInteger n') | (slice, n') <- Slice.fromLimb limb]
      )

mergeRefsAndClean :: (Integral n, Ord a) => Map a n -> Map a n -> Map a n
mergeRefsAndClean xs ys = Map.filter (/= 0) (Map.unionWith (+) xs ys)
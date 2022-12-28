{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Keelung.Data.Bindings where

import Control.DeepSeq (NFData)
import Data.Bifunctor (Bifunctor (..))
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Serialize (Serialize)
import Data.Validation
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import GHC.Generics (Generic)
import Keelung.Field.N (N (N))
import Keelung.Types

--------------------------------------------------------------------------------

-- | Data structure for data associated with different primitive datatypes
data Struct f b u = Struct
  { structF :: f,
    structB :: b,
    structU :: IntMap u
  }
  deriving (Eq, Show, NFData, Generic)

instance (Serialize f, Serialize b, Serialize u) => Serialize (Struct f b u)

instance (Semigroup f, Semigroup b, Semigroup u) => Semigroup (Struct f b u) where
  Struct f1 b1 u1 <> Struct f2 b2 u2 = Struct (f1 <> f2) (b1 <> b2) (u1 <> u2)

instance (Monoid f, Monoid b, Monoid u) => Monoid (Struct f b u) where
  mempty = Struct mempty mempty mempty

updateF :: (x -> y) -> Struct x b u -> Struct y b u
updateF func (Struct f b u) = Struct (func f) b u

updateB :: (x -> y) -> Struct f x u -> Struct f y u
updateB func (Struct f b u) = Struct f (func b) u

updateU :: Width -> (x -> x) -> Struct f b x -> Struct f b x
updateU w func (Struct f b u) = Struct f b $ IntMap.adjust func w u

empty :: (Monoid f, Eq f, Eq b, Monoid b) => Struct f b u -> Bool
empty (Struct f b u) = f == mempty && b == mempty && IntMap.null u

--------------------------------------------------------------------------------

data OIX n = OIX
  { ofO :: n,
    ofI :: n,
    ofX :: n
  }
  deriving (Eq, Show, NFData, Generic)

instance Serialize n => Serialize (OIX n)

instance (Semigroup n) => Semigroup (OIX n) where
  OIX o1 i1 x1 <> OIX o2 i2 x2 = OIX (o1 <> o2) (i1 <> i2) (x1 <> x2)

instance (Monoid n) => Monoid (OIX n) where
  mempty = OIX mempty mempty mempty

updateO :: (n -> n) -> OIX n -> OIX n
updateO f (OIX o i x) = OIX (f o) i x

updateI :: (n -> n) -> OIX n -> OIX n
updateI f (OIX o i x) = OIX o (f i) x

updateX :: (n -> n) -> OIX n -> OIX n
updateX f (OIX o i x) = OIX o i (f x)

--------------------------------------------------------------------------------

type Witness n = OIX (Struct (TotalBinding n) (TotalBinding n) (TotalBinding n))

type TotalBinding n = Vector n

--------------------------------------------------------------------------------

type VarSet n = OIX (Struct IntSet IntSet IntSet)

instance {-# OVERLAPPING #-} Show (VarSet n) where
  show (OIX o i x) =
    showList' $
      showStruct "O" o <> showStruct "I" i <> showStruct "" x
    where
      showList' :: [String] -> String
      showList' xs = "[" <> List.intercalate ", " xs <> "]"

      showStruct :: String -> Struct IntSet IntSet IntSet -> [String]
      showStruct prefix (Struct f b u) =
        map (\var -> "$B" <> prefix <> show var) (IntSet.toList b)
          <> map (\var -> "$F" <> prefix <> show var) (IntSet.toList f)
          <> concatMap (\(width, xs) -> map (\var -> "$U" <> toSubscript width <> prefix <> show var) (IntSet.toList xs)) (IntMap.toList u)

toSubscript :: Int -> String
toSubscript = map go . show
  where
    go c = case c of
      '0' -> '₀'
      '1' -> '₁'
      '2' -> '₂'
      '3' -> '₃'
      '4' -> '₄'
      '5' -> '₅'
      '6' -> '₆'
      '7' -> '₇'
      '8' -> '₈'
      '9' -> '₉'
      _ -> c

--------------------------------------------------------------------------------

-- | Data structure for interpreters
type Partial n = OIX (Struct (PartialBinding n) (PartialBinding n) (PartialBinding n))

-- | Expected number of bindings and actual bindings
type PartialBinding n = (Int, IntMap n)

instance {-# OVERLAPPING #-} (GaloisField n, Integral n) => Show (Partial n) where
  show (OIX o i x) = showList' $ showStruct "O" o <> showStruct "I" i <> showStruct "" x
    where
      showList' :: [String] -> String
      showList' xs = "[" <> List.intercalate ", " xs <> "]"

      showPartialBinding :: (GaloisField n, Integral n) => String -> (Int, IntMap n) -> IntMap String
      showPartialBinding prefix (_size, bindings) = IntMap.mapWithKey (\k v -> "$" <> prefix <> show k <> " := " <> show (N v)) bindings

      showStruct :: (GaloisField n, Integral n) => String -> Struct (PartialBinding n) (PartialBinding n) (PartialBinding n) -> [String]
      showStruct suffix (Struct f b u) =
        toList (showPartialBinding ("F" <> suffix) f)
          <> toList (showPartialBinding ("B" <> suffix) b)
          <> concatMap (\(width, xs) -> toList (showPartialBinding ("U" <> suffix <> toSubscript width) xs)) (IntMap.toList u)

-- | Convert a partial binding to a total binding, or return the variables that are not bound
toTotal :: Partial n -> Either (VarSet n) (Witness n)
toTotal (OIX o i x) =
  toEither $
    OIX
      <$> first (\struct -> OIX struct mempty mempty) (convertStruct o)
      <*> first (\struct -> OIX mempty struct mempty) (convertStruct i)
      <*> first (OIX mempty mempty) (convertStruct x)
  where
    convertStruct ::
      Struct (Int, IntMap n) (Int, IntMap n) (Int, IntMap n) ->
      Validation (Struct IntSet IntSet IntSet) (Struct (Vector n) (Vector n) (Vector n))
    convertStruct (Struct f b u) =
      Struct
        <$> first (\set -> Struct set mempty mempty) (convert f)
        <*> first (\set -> Struct mempty set mempty) (convert b)
        <*> first (Struct mempty mempty) (sequenceIntMap convert u)

    convert :: (Int, IntMap n) -> Validation IntSet (Vector n)
    convert (size, xs) =
      if IntMap.size xs < size
        then
          let completeIntSet = IntSet.fromDistinctAscList [0 .. size - 1]
           in Failure (IntSet.difference completeIntSet (IntMap.keysSet xs))
        else Success (Vector.fromList (toList xs))

    sequenceIntMap :: (a -> Validation b c) -> IntMap a -> Validation (IntMap b) (IntMap c)
    sequenceIntMap f = sequenceA . IntMap.mapWithKey (\width xs -> first (IntMap.singleton width) (f xs))

restrictVars :: Partial n -> VarSet n -> Partial n
restrictVars (OIX o i x) (OIX o' i' x') =
  OIX
    (restrictStruct o o')
    (restrictStruct i i')
    (restrictStruct x x')
  where
    restrictStruct :: Struct (PartialBinding n) (PartialBinding n) (PartialBinding n) -> Struct IntSet IntSet IntSet -> Struct (PartialBinding n) (PartialBinding n) (PartialBinding n)
    restrictStruct (Struct f b u) (Struct f' b' u') =
      Struct
        (restrict f f')
        (restrict b b')
        (IntMap.intersectionWith restrict u u')

    restrict :: (Int, IntMap n) -> IntSet -> (Int, IntMap n)
    restrict (size, xs) set = (size, IntMap.restrictKeys xs set)
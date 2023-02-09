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
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List qualified as List
import Data.Serialize (Serialize)
import Data.Validation
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import GHC.Generics (Generic)
import Keelung.Data.N (N (N))
import Keelung.Data.Struct

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

showList' :: [String] -> String
showList' xs = "[" <> List.intercalate ", " xs <> "]"

instance {-# OVERLAPPING #-} Show (VarSet n) where
  show (OIX o i x) =
    showList' $
      showStruct "O" o <> showStruct "I" i <> showStruct "" x
    where
      showStruct :: String -> Struct IntSet IntSet IntSet -> [String]
      showStruct prefix (Struct f b u) =
        map (\var -> "B" <> prefix <> show var) (IntSet.toList b)
          <> map (\var -> "F" <> prefix <> show var) (IntSet.toList f)
          <> concatMap (\(width, xs) -> map (\var -> "U" <> toSubscript width <> prefix <> show var) (IntSet.toList xs)) (IntMap.toList u)

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
      showPartialBinding :: (GaloisField n, Integral n) => String -> (Int, IntMap n) -> IntMap String
      showPartialBinding prefix (_size, bindings) = IntMap.mapWithKey (\k v -> prefix <> show k <> " := " <> show (N v)) bindings

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
        <$> first (\set -> Struct set mempty mempty) (toTotal' f)
        <*> first (\set -> Struct mempty set mempty) (toTotal' b)
        <*> first (Struct mempty mempty) (sequenceIntMap toTotal' u)

    sequenceIntMap :: (a -> Validation b c) -> IntMap a -> Validation (IntMap b) (IntMap c)
    sequenceIntMap f = sequenceA . IntMap.mapWithKey (\width xs -> first (IntMap.singleton width) (f xs))

toTotal' :: (Int, IntMap n) -> Validation IntSet (Vector n)
toTotal' (size, xs) =
  if IntMap.size xs < size
    then
      let completeIntSet = IntSet.fromDistinctAscList [0 .. size - 1]
       in Failure (IntSet.difference completeIntSet (IntMap.keysSet xs))
    else Success (Vector.fromList (toList xs))

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
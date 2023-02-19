{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Keelung.Data.Witness where

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
import Keelung.Syntax (Width)

--------------------------------------------------------------------------------

-- | Homogeneous version of 'Struct'
data HStruct a = HStruct a a (IntMap a)
  deriving (Eq, Show, Generic)

instance NFData a => NFData (HStruct a)

instance Functor HStruct where
  fmap func (HStruct f b u) = HStruct (func f) (func b) (fmap func u)

instance Foldable HStruct where
  foldMap func (HStruct f b u) = func f <> func b <> foldMap func u

instance Semigroup a => Semigroup (HStruct a) where
  HStruct f1 b1 u1 <> HStruct f2 b2 u2 =
    HStruct (f1 <> f2) (b1 <> b2) (u1 <> u2)

instance Monoid a => Monoid (HStruct a) where
  mempty = HStruct mempty mempty mempty

instance Serialize n => Serialize (HStruct n)

--------------------------------------------------------------------------------

class HasF a f | a -> f where
  getF :: a -> f
  setF :: f -> a -> a
  modifyF :: (f -> f) -> a -> a

instance HasF (HStruct f) f where
  getF (HStruct f _ _) = f
  setF f (HStruct _ b u) = HStruct f b u
  modifyF func (HStruct f b u) = HStruct (func f) b u

instance HasF (Struct f b u) f where
  getF (Struct f _ _) = f
  setF f (Struct _ b u) = Struct f b u
  modifyF func (Struct f b u) = Struct (func f) b u

--------------------------------------------------------------------------------

class HasB a b | a -> b where
  getB :: a -> b
  setB :: b -> a -> a
  modifyB :: (b -> b) -> a -> a

instance HasB (HStruct b) b where
  getB (HStruct _ b _) = b
  setB b (HStruct f _ u) = HStruct f b u
  modifyB func (HStruct f b u) = HStruct f (func b) u

instance HasB (Struct f b u) b where
  getB (Struct _ b _) = b
  setB b (Struct f _ u) = Struct f b u
  modifyB func (Struct f b u) = Struct f (func b) u

--------------------------------------------------------------------------------

class HasU a u | a -> u where
  getU :: Width -> a -> Maybe u
  setU :: Width -> u -> a -> a
  modifyU :: Width -> (u -> u) -> a -> a

instance HasU (HStruct u) u where
  getU width (HStruct _ _ u) = IntMap.lookup width u
  setU width u (HStruct f b u') = HStruct f b (IntMap.insert width u u')
  modifyU width func (HStruct f b u) = HStruct f b (IntMap.adjust func width u)

--------------------------------------------------------------------------------

data Rows n = Rows
  { ofO :: n,
    ofI :: n,
    ofP :: n,
    ofX :: n
  }
  deriving (Eq, Show, NFData, Generic, Functor)

instance Serialize n => Serialize (Rows n)

instance (Semigroup n) => Semigroup (Rows n) where
  Rows o1 i1 p1 x1 <> Rows o2 i2 p2 x2 =
    Rows (o1 <> o2) (i1 <> i2) (p1 <> p2) (x1 <> x2)

instance (Monoid n) => Monoid (Rows n) where
  mempty = Rows mempty mempty mempty mempty

updateO :: (n -> n) -> Rows n -> Rows n
updateO f (Rows o i p x) = Rows (f o) i p x

updateI :: (n -> n) -> Rows n -> Rows n
updateI f (Rows o i p x) = Rows o (f i) p x

updateP :: (n -> n) -> Rows n -> Rows n
updateP f (Rows o i p x) = Rows o i (f p) x

updateX :: (n -> n) -> Rows n -> Rows n
updateX f (Rows o i p x) = Rows o i p (f x)

--------------------------------------------------------------------------------

type Witness n = Rows (HStruct (Vector n))

type TotalBinding n = Vector n

--------------------------------------------------------------------------------

type VarSet n = Rows (HStruct IntSet)

showList' :: [String] -> String
showList' xs = "[" <> List.intercalate ", " xs <> "]"

instance {-# OVERLAPPING #-} Show (VarSet n) where
  show (Rows o i p x) =
    showList' $
      showStruct "O" o <> showStruct "I" i <> showStruct "P" p <> showStruct "" x
    where
      showStruct :: String -> HStruct IntSet -> [String]
      showStruct prefix (HStruct f b u) =
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
type Partial n = Rows (HStruct (PartialBinding n))

-- | Expected number of bindings and actual bindings
type PartialBinding n = (Int, IntMap n)

instance {-# OVERLAPPING #-} (GaloisField n, Integral n) => Show (Partial n) where
  show (Rows o i p x) = showList' $ showStruct "O" o <> showStruct "I" i <> showStruct "P" p <> showStruct "" x
    where
      showPartialBinding :: (GaloisField n, Integral n) => String -> (Int, IntMap n) -> IntMap String
      showPartialBinding prefix (_size, bindings) = IntMap.mapWithKey (\k v -> prefix <> show k <> " := " <> show (N v)) bindings

      showStruct :: (GaloisField n, Integral n) => String -> HStruct (PartialBinding n) -> [String]
      showStruct suffix (HStruct f b u) =
        toList (showPartialBinding ("F" <> suffix) f)
          <> toList (showPartialBinding ("B" <> suffix) b)
          <> concatMap (\(width, xs) -> toList (showPartialBinding ("U" <> suffix <> toSubscript width) xs)) (IntMap.toList u)

-- | Convert a partial binding to a total binding, or return the variables that are not bound
toTotal :: Partial n -> Either (VarSet n) (Witness n)
toTotal (Rows o i p x) =
  toEither $
    Rows
      <$> first (\struct -> Rows struct mempty mempty mempty) (convertStruct o)
      <*> first (\struct -> Rows mempty struct mempty mempty) (convertStruct i)
      <*> first (\struct -> Rows mempty mempty struct mempty) (convertStruct p)
      <*> first (Rows mempty mempty mempty) (convertStruct x)
  where
    convertStruct ::
      HStruct (PartialBinding n) ->
      Validation (HStruct IntSet) (HStruct (Vector n))
    convertStruct (HStruct f b u) =
      HStruct
        <$> first (\set -> HStruct set mempty mempty) (toTotal' f)
        <*> first (\set -> HStruct mempty set mempty) (toTotal' b)
        <*> first (HStruct mempty mempty) (sequenceIntMap toTotal' u)

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
restrictVars (Rows o i p x) (Rows o' i' p' x') =
  Rows
    (restrictStruct o o')
    (restrictStruct i i')
    (restrictStruct p p')
    (restrictStruct x x')
  where
    restrictStruct :: HStruct (PartialBinding n) -> HStruct IntSet -> HStruct (PartialBinding n)
    restrictStruct (HStruct f b u) (HStruct f' b' u') =
      HStruct
        (restrict f f')
        (restrict b b')
        (IntMap.intersectionWith restrict u u')

    restrict :: (Int, IntMap n) -> IntSet -> (Int, IntMap n)
    restrict (size, xs) set = (size, IntMap.restrictKeys xs set)
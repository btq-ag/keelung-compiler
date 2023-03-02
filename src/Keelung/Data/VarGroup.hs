{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Keelung.Data.VarGroup where

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
data VarGroup a = VarGroup a a (IntMap a)
  deriving (Eq, Show, Generic)

instance NFData a => NFData (VarGroup a)

instance Functor VarGroup where
  fmap func (VarGroup f b u) = VarGroup (func f) (func b) (fmap func u)

instance Foldable VarGroup where
  foldMap func (VarGroup f b u) = func f <> func b <> foldMap func u

instance Semigroup a => Semigroup (VarGroup a) where
  VarGroup f1 b1 u1 <> VarGroup f2 b2 u2 =
    VarGroup (f1 <> f2) (b1 <> b2) (u1 <> u2)

instance Monoid a => Monoid (VarGroup a) where
  mempty = VarGroup mempty mempty mempty

instance Serialize n => Serialize (VarGroup n)

--------------------------------------------------------------------------------

class HasF a f | a -> f where
  getF :: a -> f
  putF :: f -> a -> a
  modifyF :: (f -> f) -> a -> a

instance HasF (VarGroup f) f where
  getF (VarGroup f _ _) = f
  putF f (VarGroup _ b u) = VarGroup f b u
  modifyF func (VarGroup f b u) = VarGroup (func f) b u

instance HasF (Struct f b u) f where
  getF (Struct f _ _) = f
  putF f (Struct _ b u) = Struct f b u
  modifyF func (Struct f b u) = Struct (func f) b u

--------------------------------------------------------------------------------

class HasB a b | a -> b where
  getB :: a -> b
  putB :: b -> a -> a
  modifyB :: (b -> b) -> a -> a

instance HasB (VarGroup b) b where
  getB (VarGroup _ b _) = b
  putB b (VarGroup f _ u) = VarGroup f b u
  modifyB func (VarGroup f b u) = VarGroup f (func b) u

instance HasB (Struct f b u) b where
  getB (Struct _ b _) = b
  putB b (Struct f _ u) = Struct f b u
  modifyB func (Struct f b u) = Struct f (func b) u

--------------------------------------------------------------------------------

class HasU a u | a -> u where
  getU :: Width -> a -> Maybe u
  putU :: Width -> u -> a -> a
  modifyU :: Width -> (u -> u) -> a -> a

instance HasU (VarGroup u) u where
  getU width (VarGroup _ _ u) = IntMap.lookup width u
  putU width u (VarGroup f b u') = VarGroup f b (IntMap.insert width u u')
  modifyU width func (VarGroup f b u) = VarGroup f b (IntMap.adjust func width u)

--------------------------------------------------------------------------------

data VarGroups n = VarGroups
  { ofO :: n,
    ofI :: n,
    ofP :: n,
    ofX :: n
  }
  deriving (Eq, Show, NFData, Generic, Functor)

instance Serialize n => Serialize (VarGroups n)

instance (Semigroup n) => Semigroup (VarGroups n) where
  VarGroups o1 i1 p1 x1 <> VarGroups o2 i2 p2 x2 =
    VarGroups (o1 <> o2) (i1 <> i2) (p1 <> p2) (x1 <> x2)

instance (Monoid n) => Monoid (VarGroups n) where
  mempty = VarGroups mempty mempty mempty mempty

updateO :: (n -> n) -> VarGroups n -> VarGroups n
updateO f (VarGroups o i p x) = VarGroups (f o) i p x

updateI :: (n -> n) -> VarGroups n -> VarGroups n
updateI f (VarGroups o i p x) = VarGroups o (f i) p x

updateP :: (n -> n) -> VarGroups n -> VarGroups n
updateP f (VarGroups o i p x) = VarGroups o i (f p) x

updateX :: (n -> n) -> VarGroups n -> VarGroups n
updateX f (VarGroups o i p x) = VarGroups o i p (f x)

--------------------------------------------------------------------------------

type Witness n = VarGroups (VarGroup (Vector n))

--------------------------------------------------------------------------------

type VarSet n = VarGroups (VarGroup IntSet)

showList' :: [String] -> String
showList' xs = "[" <> List.intercalate ", " xs <> "]"

instance {-# OVERLAPPING #-} Show (VarSet n) where
  show (VarGroups o i p x) =
    showList' $
      showVarGroup "O" o <> showVarGroup "I" i <> showVarGroup "P" p <> showVarGroup "X" x
    where
      showVarGroup :: String -> VarGroup IntSet -> [String]
      showVarGroup prefix (VarGroup f b u) =
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
type Partial n = VarGroups (VarGroup (PartialBinding n))

-- | Expected number of bindings and actual bindings
type PartialBinding n = (Int, IntMap n)

instance {-# OVERLAPPING #-} (GaloisField n, Integral n) => Show (Partial n) where
  show (VarGroups o i p x) = showList' $ showVarGroup "O" o <> showVarGroup "I" i <> showVarGroup "P" p <> showVarGroup "" x
    where
      showPartialBinding :: (GaloisField n, Integral n) => String -> (Int, IntMap n) -> IntMap String
      showPartialBinding prefix (_size, bindings) = IntMap.mapWithKey (\k v -> prefix <> show k <> " := " <> show (N v)) bindings

      showVarGroup :: (GaloisField n, Integral n) => String -> VarGroup (PartialBinding n) -> [String]
      showVarGroup suffix (VarGroup f b u) =
        toList (showPartialBinding ("F" <> suffix) f)
          <> toList (showPartialBinding ("B" <> suffix) b)
          <> concatMap (\(width, xs) -> toList (showPartialBinding ("U" <> suffix <> toSubscript width) xs)) (IntMap.toList u)

-- | Convert a partial binding to a total binding, or return the variables that are not bound
toTotal :: Partial n -> Either (VarSet n) (Witness n)
toTotal (VarGroups o i p x) =
  toEither $
    VarGroups
      <$> first (\struct -> VarGroups struct mempty mempty mempty) (convertVarGroup o)
      <*> first (\struct -> VarGroups mempty struct mempty mempty) (convertVarGroup i)
      <*> first (\struct -> VarGroups mempty mempty struct mempty) (convertVarGroup p)
      <*> first (VarGroups mempty mempty mempty) (convertVarGroup x)
  where
    convertVarGroup ::
      VarGroup (PartialBinding n) ->
      Validation (VarGroup IntSet) (VarGroup (Vector n))
    convertVarGroup (VarGroup f b u) =
      VarGroup
        <$> first (\set -> VarGroup set mempty mempty) (toTotal' f)
        <*> first (\set -> VarGroup mempty set mempty) (toTotal' b)
        <*> first (VarGroup mempty mempty) (sequenceIntMap toTotal' u)

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
restrictVars (VarGroups o i p x) (VarGroups o' i' p' x') =
  VarGroups
    (restrictVarGroup o o')
    (restrictVarGroup i i')
    (restrictVarGroup p p')
    (restrictVarGroup x x')
  where
    restrictVarGroup :: VarGroup (PartialBinding n) -> VarGroup IntSet -> VarGroup (PartialBinding n)
    restrictVarGroup (VarGroup f b u) (VarGroup f' b' u') =
      VarGroup
        (restrict f f')
        (restrict b b')
        (IntMap.intersectionWith restrict u u')

    restrict :: (Int, IntMap n) -> IntSet -> (Int, IntMap n)
    restrict (size, xs) set = (size, IntMap.restrictKeys xs set)
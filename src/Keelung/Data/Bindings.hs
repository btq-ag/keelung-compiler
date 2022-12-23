{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Keelung.Data.Bindings where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Maybe (isNothing)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Keelung.Types
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Data.Serialize (Serialize)

--------------------------------------------------------------------------------
type Total n = Bindings (Binding (Vector n)) (Binding (Vector n)) (Binding (Vector n))

type Partial n = Bindings (Binding (Vector (Maybe n))) (Binding (Vector (Maybe n))) (Binding (Vector (Maybe n)))

type Sparse n = Bindings (Binding (IntMap n)) (Binding (IntMap n)) (Binding (IntMap n))

type Vars n = Bindings (Binding IntSet) (Binding IntSet) (Binding IntSet)

-- | Convert a partial binding to a total binding, or return the variables that are not bound
toTotal :: Partial n -> Either (Vars n) (Total n)
toTotal (Bindings f b u) =
  let -- 1. convert the partial binding to a total binding
      -- 2. collect the variables that are not bound
      (fK, fV) = splitPair $ fmap collectNothings f
      (bK, bV) = splitPair $ fmap collectNothings b
      (uK, uV) = splitIntMap $ fmap (splitPair . fmap collectNothings) u
      -- tally the number of variables that are not bound
      fKSize = varsSize fK
      bKSize = varsSize bK
      uKSize = sum $ fmap varsSize uK
   in if fKSize + bKSize + uKSize == 0
        then Right $ Bindings fV bV uV
        else Left $ Bindings fK bK uK
  where
    collectNothings :: Vector (Maybe n) -> (IntSet, Vector n)
    collectNothings xs = (IntSet.fromList $ Vector.toList $ Vector.findIndices isNothing xs, Vector.mapMaybe id xs)

    splitIntMap :: IntMap (a, b) -> (IntMap a, IntMap b)
    splitIntMap m = (IntMap.map fst m, IntMap.map snd m)

    varsSize :: Binding IntSet -> Int
    varsSize (Binding i o x) = IntSet.size i + IntSet.size o + IntSet.size x

--------------------------------------------------------------------------------

-- | Binding of a single datatype
data Binding n = Binding
  { ofI :: n,
    ofO :: n,
    ofX :: n
  }
  deriving (Eq, Show, NFData, Generic)

instance Semigroup n => Semigroup (Binding n) where
  Binding i1 o1 x1 <> Binding i2 o2 x2 = Binding (i1 <> i2) (o1 <> o2) (x1 <> x2)

instance Monoid n => Monoid (Binding n) where
  mempty = Binding mempty mempty mempty

instance Foldable Binding where
  foldMap f (Binding i o x) = f i <> f o <> f x

instance Functor Binding where
  fmap f (Binding i o x) = Binding (f i) (f o) (f x)

instance Traversable Binding where
  traverse f (Binding i o x) = Binding <$> f i <*> f o <*> f x

instance Serialize n => Serialize (Binding n)

updateX :: (n -> n) -> Binding n -> Binding n
updateX f (Binding i o x) = Binding i o (f x)

updateO :: (n -> n) -> Binding n -> Binding n
updateO f (Binding i o x) = Binding i (f o) x

updateI :: (n -> n) -> Binding n -> Binding n
updateI f (Binding i o x) = Binding (f i) o x

splitPair :: Binding (a, b) -> (Binding a, Binding b)
splitPair (Binding (i1, i2) (o1, o2) (x1, x2)) = (Binding i1 o1 x1, Binding i2 o2 x2)

--------------------------------------------------------------------------------

-- | Bindings of different datatypes
data Bindings f b u = Bindings
  { ofF :: f,
    ofB :: b,
    ofU :: IntMap u
  }
  deriving (Eq, Show, NFData, Generic)

instance (Semigroup f, Semigroup b, Semigroup u) => Semigroup (Bindings f b u) where
  Bindings f1 b1 u1 <> Bindings f2 b2 u2 = Bindings (f1 <> f2) (b1 <> b2) (u1 <> u2)

instance (Monoid f, Monoid b, Monoid u) => Monoid (Bindings f b u) where
  mempty = Bindings mempty mempty mempty

instance (Serialize f, Serialize b, Serialize u) => Serialize (Bindings f b u)

updateF :: (f -> f) -> Bindings f b u -> Bindings f b u
updateF f (Bindings f' b u) = Bindings (f f') b u

updateB :: (b -> b) -> Bindings f b u -> Bindings f b u
updateB f (Bindings f' b u) = Bindings f' (f b) u

updateU :: Width -> (u -> u) -> Bindings f b u -> Bindings f b u
updateU w f (Bindings f' b u) = Bindings f' b $ IntMap.adjust f w u
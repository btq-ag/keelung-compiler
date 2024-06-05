{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Keelung.Data.Dict (DictKey (..), Dict (..)) where

import Control.DeepSeq (NFData)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Keelung.Data.Reference (Ref)

class DictKey k where
  data Dict k :: Type -> Type

  empty :: Dict k v
  lookup :: k -> Dict k v -> Maybe v
  insert :: k -> v -> Dict k v -> Dict k v
  toList :: Dict k v -> [(k, v)]
  mapMaybe :: (v -> Maybe w) -> Dict k v -> Dict k w
  size :: Dict k v -> Int
  foldlWithKey :: (a -> k -> v -> a) -> a -> Dict k v -> a
  filterWithKey :: (k -> v -> Bool) -> Dict k v -> Dict k v
  keys :: Dict k v -> [k]

instance DictKey Int where
  newtype Dict Int v = IntDict (IntMap v)
    deriving (Show, Eq, Generic, NFData, Functor)

  empty = IntDict IntMap.empty
  lookup k (IntDict m) = IntMap.lookup k m
  insert k v (IntDict m) = IntDict (IntMap.insert k v m)
  toList (IntDict m) = IntMap.toList m
  mapMaybe f (IntDict m) = IntDict (IntMap.mapMaybe f m)
  size (IntDict m) = IntMap.size m
  foldlWithKey f a (IntDict m) = IntMap.foldlWithKey' f a m
  filterWithKey f (IntDict m) = IntDict (IntMap.filterWithKey f m)
  keys (IntDict m) = IntMap.keys m

instance Semigroup (Dict Int v) where
  IntDict m1 <> IntDict m2 = IntDict (m1 <> m2)

instance Monoid (Dict Int v) where
  mempty = IntDict mempty

instance Foldable (Dict Int) where
  foldr f a (IntDict m) = IntMap.foldr f a m

instance DictKey Ref where
  newtype Dict Ref v = RefDict (Map Ref v)
    deriving (Show, Eq, Generic, NFData, Functor)
  empty = RefDict Map.empty
  lookup k (RefDict m) = Map.lookup k m
  insert k v (RefDict m) = RefDict (Map.insert k v m)
  toList (RefDict m) = Map.toList m
  mapMaybe f (RefDict m) = RefDict (Map.mapMaybe f m)
  size (RefDict m) = Map.size m
  foldlWithKey f a (RefDict m) = Map.foldlWithKey' f a m
  filterWithKey f (RefDict m) = RefDict (Map.filterWithKey f m)
  keys (RefDict m) = Map.keys m

instance Semigroup (Dict Ref v) where
  RefDict m1 <> RefDict m2 = RefDict (m1 <> m2)

instance Monoid (Dict Ref v) where
  mempty = RefDict mempty

instance Foldable (Dict Ref) where
  foldr f a (RefDict m) = Map.foldr f a m
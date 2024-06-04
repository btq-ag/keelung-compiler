{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module Keelung.Data.UnionFind (UnionFind (..), Lookup (..)) where

import Data.Kind (Type)
import Keelung.Data.UnionFind.Type

class UnionFind var val where
  data Map var val :: Type
  data Rel val :: Type

  new :: Map var val

  assign :: var -> val -> Map var val -> Maybe (Map var val)

  relate :: var -> var -> Rel val -> Map var val -> Maybe (Map var val)

  lookup :: var -> Map var val -> Lookup var val (Rel val)

-- -- | Interface for a union-find data structure.
-- class UnionFind a var val rel where
--   -- | Construct a new union-find data structure.
--   new :: a val

--   -- | Assign a value to a variable. Returns `Nothing` if nothing changed.
--   assign :: var -> val -> a val -> Maybe (a val)

--   -- | Relate two variables with a relation. Returns `Nothing` if nothing changed.
--   relate :: var -> var -> rel -> a val -> Maybe (a val)

--   -- | Lookup a variable and see if it's a constant, root, or child of another variable.
--   lookup :: var -> a val -> Lookup var val rel

--------------------------------------------------------------------------------

-- instance (GaloisField n, Integral n) => UnionFind Field.UnionFind Var n (Field.LinRel n) where
--   new = Field.new
--   assign = Field.assign
--   relate = Field.relate
--   lookup = Field.lookup

-- class GMapKey k where
--   data GMap k :: * -> *
--   empty       :: GMap k v
--   -- lookup      :: k -> GMap k v -> Maybe v
--   insert      :: k -> v -> GMap k v -> GMap k v

-- instance GMapKey Int where
--   data GMap Int v        = GMapInt (Data.IntMap.IntMap v)
--   empty                  = GMapInt Data.IntMap.empty
--   -- lookup k   (GMapInt m) = Data.IntMap.lookup k m
--   insert k v (GMapInt m) = GMapInt (Data.IntMap.insert k v m)
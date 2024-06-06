{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Data.UnionFind.Type (Lookup (..), Status (..)) where

import Data.IntMap.Strict (IntMap)
import GHC.Generics (Generic)
import Keelung (Var)

-- | Lookup result for a variable.
data Lookup var val rel
  = -- | The variable is a constant.
    Constant val
  | -- | The variable is a root.
    Root
  | -- | The variable is a child of another variable. `parent = rel child`
    ChildOf var rel
  deriving (Show, Eq, Generic, Functor)

-- | Status of a variable in a union-find data structure.
data Status n rel
  = IsConstant n
  | IsRoot
      (IntMap rel) -- mappping from the child to the relation
  | IsChildOf
      Var -- parent
      rel -- relation such that `child = relation parent`
  deriving (Show, Eq, Generic, Functor)
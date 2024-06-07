{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Data.UnionFind.Type
  ( Lookup (..),
    Status (..),
    UnionFind (..),
    new,
    Error (..),
  )
where

import Data.IntMap.Strict (IntMap)
import Data.IntSet (IntSet)
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
data Status val rel
  = IsConstant val
  | IsRoot
      (IntMap rel) -- mappping from the child to the relation
  | IsChildOf
      Var -- parent
      rel -- relation such that `child = relation parent`
  deriving (Show, Eq, Generic, Functor)

--------------------------------------------------------------------------------

newtype UnionFind val rel = UnionFind {unUnionFind :: IntMap (Status val rel)} deriving (Show, Eq)

-- instance Show (UnionFind val rel) where
--   show (UnionFind relations) =
--     "UnionFind\n"
--       <> mconcat (map (<> "\n") (concatMap toString (IntMap.toList relations)))
--     where
--       showVar var = let varString = "$" <> show var in "  " <> varString <> replicate (8 - length varString) ' '

--       toString (var, IsConstant value) = [showVar var <> " = " <> show value]
--       toString (var, IsRoot toChildren) = case map renderLinRel (IntMap.toList toChildren) of
--         [] -> [showVar var <> " = []"] -- should never happen
--         (x : xs) -> showVar var <> " = " <> x : map ("           = " <>) xs
--       toString (_var, IsChildOf _parent _relation) = []

-- | Create an empty UnionFind data structure.
new :: UnionFind val rel
new = UnionFind mempty

--------------------------------------------------------------------------------

-- | For testing the validity of the data structure
data Error
  = RootNotSenior Var IntSet
  | ChildrenNotRecognizingParent Var IntSet
  deriving (Show, Eq)

--------------------------------------------------------------------------------

{-# LANGUAGE FunctionalDependencies #-}

module Keelung.Data.UnionFind.Relation where

import Keelung (Var)

-- | Interface for a relation between variables.
--   Semigroup for relation composition and Monoid for identity.
class (Semigroup a, Monoid a) => Relation a val | a -> val where
  -- | Calculates the inverse of a relation.
  invert :: a -> a

  -- | Executes the relation on a value.
  execute :: a -> val -> val

  -- | Render the relation with a variable.
  renderWithVar :: Var -> a -> String
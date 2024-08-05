{-# LANGUAGE FunctionalDependencies #-}

module Keelung.Data.UnionFind.Relation where

-- | Interface for a relation between variables.
--   Semigroup for relation composition and Monoid for identity.
class (Semigroup a, Monoid a) => Relation a val | a -> val where
  -- | Calculates the inverse of a relation.
  invert :: a -> a

  -- | Executes the relation on a value.
  execute :: a -> val -> val

  -- | Render the relation with a string representing a variable.
  renderWithVarString :: String -> a -> String
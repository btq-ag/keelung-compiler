{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Data.UnionFind.Relation where

-- | Interface for a relation between variables.
--   Semigroup for relation composition and Monoid for identity.
class (Semigroup a, Monoid a) => IsRelation a where
  -- | Calculates the inverse of a relation.
  invert :: a -> a

  -- -- | Executes the relation on a value.
  -- execute :: a -> val -> val

  -- | Render the relation with a string representing a variable.
  renderWithVarString :: String -> a -> String

class ExecRelation a val where
  -- | Executes the relation on a value.
  execute :: a -> val -> val
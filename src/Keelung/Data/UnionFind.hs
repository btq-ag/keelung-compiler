{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Keelung.Data.UnionFind (UnionFind (..), Lookup (..)) where

import Data.Kind (Type)
import Keelung.Data.UnionFind.Type
import Keelung.Data.Dict (Dict)

-- | Interface for a union-find data structure.
class UnionFind var val where
  -- | Internal data structure for variable relation bookkeeping
  -- type Dict var a

  -- | Wrapper type for the data structure
  data Map var val :: Type

  -- | Relation between variables
  data Rel val :: Type

  -- | Construct a new union-find data structure.
  new :: Map var val

  -- | Assign a value to a variable. Returns `Nothing` if nothing changed.
  assign :: var -> val -> Map var val -> Maybe (Map var val)

  -- | Relate two variables with a relation. Returns `Nothing` if nothing changed.
  relate :: var -> var -> Rel val -> Map var val -> Maybe (Map var val)

  -- | Lookup a variable and see if it's a constant, root, or child of another variable.
  lookup :: var -> Map var val -> Lookup var val (Rel val)

  -- | Exports the UnionFind as a pair of:
  --    1. a map from the constant variables to their values
  --    2. a map from the root variables to their children with the relation (from parent to child)
  export ::
    Map var val ->
    ( Dict var val, -- constants
      Dict var (Dict var (Rel val)) -- families
    )


-- -- | Helper function for rendering the families resulted from `export`
-- renderFamilies :: (GaloisField n, Integral n) => Dict var (Dict var (Rel val)) -> String
-- renderFamilies families = mconcat (map (<> "\n") (concatMap toString (IntMap.toList families)))
--   where
--     showVar var = let varString = "$" <> show var in "  " <> varString <> replicate (8 - length varString) ' '
--     toString (root, toChildren) = case map renderLinRel (IntMap.toList (fmap (uncurry LinRel) toChildren)) of
--       [] -> [showVar root <> " = []"] -- should never happen
--       (x : xs) -> showVar root <> " = " <> x : map ("           = " <>) xs

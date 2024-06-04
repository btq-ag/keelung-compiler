module Keelung.Data.UnionFind.Type (Lookup (..)) where

-- | Lookup result for a variable.
data Lookup var val rel
  = -- | The variable is a constant.
    Constant val
  | -- | The variable is a root.
    Root
  | -- | The variable is a child of another variable. `parent = rel child`
    ChildOf var rel
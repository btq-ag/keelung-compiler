{-# LANGUAGE MultiParamTypeClasses #-}
{-# HLINT ignore "Use list comprehension" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Data.UnionFind.Boolean
  ( -- * Construction
    UnionFind,
    new,

    -- * Operations
    assign,
    relate,

    -- * Lookup
    Lookup (..),
    export,

    -- * Relation
    Rel (..),

    -- * Testing
    Error (..),
    isValid,
    validate,
  )
where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Keelung.Data.UnionFind
import Keelung.Data.UnionFind.Relation (ExecRelation (..), IsRelation (..))
import Prelude hiding (lookup)

--------------------------------------------------------------------------------

-- | Export the UnionFind data structure to assignements and relations.
export :: UnionFind Bool Rel -> (IntMap Bool, [(IntSet, IntSet)])
export (UnionFind xs) = (IntMap.mapMaybe f xs, map (\(k, (ys, zs)) -> (IntSet.insert k ys, zs)) (IntMap.toList (IntMap.mapMaybe g xs)))
  where
    f (IsConstant b) = Just b
    f _ = Nothing
    g (IsRoot _ children) = Just (IntMap.keysSet (IntMap.filter unRel children), IntMap.keysSet (IntMap.filter (not . unRel) children))
    g _ = Nothing

--------------------------------------------------------------------------------

newtype Rel = Rel {unRel :: Bool}
  deriving (Show, Eq)

-- | Composition of relations.
instance Semigroup Rel where
  Rel a <> Rel b = Rel (a /= b) -- XOR

-- | Identity element for `Rel`.
instance Monoid Rel where
  mempty = Rel True

instance IsRelation Rel where
  invert (Rel x) = Rel (not x)
  renderWithVarString child (Rel True) = "$" <> child
  renderWithVarString child (Rel False) = "¬$" <> child

instance ExecRelation Rel Bool where
  execute (Rel x) val = x == val -- NXOR

--------------------------------------------------------------------------------

-- | Ranges have no meaning for `Bool`.
instance HasRange Bool where
  isWithinRange _ _ = True
  execRelOnRange _ = id
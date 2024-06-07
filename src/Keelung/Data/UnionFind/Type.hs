{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use list comprehension" #-}

module Keelung.Data.UnionFind.Type where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung (Var)
import Keelung.Compiler.Relations.Monad (Seniority (..))
import Keelung.Data.UnionFind.Relation (Relation)
import Keelung.Data.UnionFind.Relation qualified as Relation

--------------------------------------------------------------------------------

-- | Lookup result for a variable.
data Lookup var val rel
  = -- | The variable is a constant.
    Constant val
  | -- | The variable is a root.
    Root
  | -- | The variable is a child of another variable. `parent = rel child`
    ChildOf var rel
  deriving (Show, Eq, Generic, Functor)

-- | Result of looking up a variable in the Relations
lookup :: Var -> UnionFind val rel -> Lookup Var val rel
lookup var relations =
  case lookupStatus var relations of
    IsConstant value -> Constant value
    IsRoot _ -> Root
    IsChildOf parent relation -> ChildOf parent relation

--------------------------------------------------------------------------------

-- | Status of a variable in a union-find data structure.
data Status val rel
  = IsConstant val
  | IsRoot
      (IntMap rel) -- mappping from the child to the relation
  | IsChildOf
      Var -- parent
      rel -- relation such that `child = relation parent`
  deriving (Show, Eq, Generic, Functor)

instance (Serialize val, Serialize rel) => Serialize (Status val rel)

--------------------------------------------------------------------------------

newtype UnionFind val rel = UnionFind {unUnionFind :: IntMap (Status val rel)} deriving (Eq, Generic)

instance (Serialize val, Serialize rel) => Serialize (UnionFind val rel)

instance (Show val, Relation rel val) => Show (UnionFind val rel) where
  show (UnionFind relations) =
    "UnionFind\n"
      <> mconcat (map (<> "\n") (concatMap toString (IntMap.toList relations)))
    where
      showVar var = let varString = "$" <> show var in "  " <> varString <> replicate (8 - length varString) ' '

      toString (var, IsConstant value) = [showVar var <> " = " <> show value]
      toString (var, IsRoot toChildren) = case map (uncurry Relation.renderWithVar) (IntMap.toList toChildren) of
        [] -> [showVar var <> " = []"] -- should never happen
        (x : xs) -> showVar var <> " = " <> x : map ("           = " <>) xs
      toString (_var, IsChildOf _parent _relation) = []

-- | Create an empty UnionFind data structure.
new :: UnionFind val rel
new = UnionFind mempty

-- | Returns the number of variables in the Reference, O(1)
size :: UnionFind val rel -> Int
size = IntMap.size . unUnionFind

-- | Returns the result of looking up a variable, O(lg n)
lookupStatus :: Var -> UnionFind val rel -> Status val rel
lookupStatus var (UnionFind relations) = case IntMap.lookup var relations of
  Nothing -> IsRoot mempty
  Just result -> result

--------------------------------------------------------------------------------

-- | For testing the validity of the data structure
data Error
  = RootNotSenior Var IntSet
  | ChildrenNotRecognizingParent Var IntSet
  deriving (Show, Eq)

-- | The data structure is valid if:
--    1. all children of a parent recognize the parent as their parent
--    2. the seniority of the root of a family is greater than equal the seniority of all its children
validate :: (Eq rel) => UnionFind val rel -> [Error]
validate relations = allChildrenRecognizeTheirParent relations <> rootsAreSenior relations

-- | Derived from `validate`
isValid :: (Eq rel) => UnionFind val rel -> Bool
isValid = null . validate

-- | A Reference is valid if all children of a parent recognize the parent as their parent
allChildrenRecognizeTheirParent :: (Eq rel) => UnionFind val rel -> [Error]
allChildrenRecognizeTheirParent relations =
  let families = IntMap.mapMaybe isParent (unUnionFind relations)

      isParent (IsRoot children) = Just children
      isParent _ = Nothing

      recognizeParent parent child relation = case lookupStatus child relations of
        IsChildOf parent' relation' -> parent == parent' && relation == relation'
        _ -> False
      childrenNotRecognizeParent parent = IntMap.filterWithKey (\child status -> not $ recognizeParent parent child status)
   in --  . IntMap.elems . IntMap.mapWithKey (recognizeParent parent)
      concatMap
        ( \(parent, children) ->
            let badChildren = childrenNotRecognizeParent parent children
             in if null badChildren then [] else [ChildrenNotRecognizingParent parent (IntMap.keysSet badChildren)]
        )
        $ IntMap.toList families

-- | A Reference is valid if the seniority of the root of a family is greater than equal the seniority of all its children
rootsAreSenior :: UnionFind val rel -> [Error]
rootsAreSenior = IntMap.foldlWithKey' go [] . unUnionFind
  where
    go :: [Error] -> Var -> Status val rel -> [Error]
    go acc _ (IsConstant _) = acc
    go acc var (IsRoot children) =
      let badChildren = IntSet.filter (\child -> compareSeniority var child == LT) (IntMap.keysSet children)
       in if IntSet.null badChildren then acc else RootNotSenior var badChildren : acc
    go acc var (IsChildOf parent _) = if compareSeniority parent var /= LT then acc else RootNotSenior parent (IntSet.singleton var) : acc
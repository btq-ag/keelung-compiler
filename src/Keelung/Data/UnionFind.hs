{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use list comprehension" #-}

module Keelung.Data.UnionFind where

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

-- | Assigns a value to a variable, O(lg n)
assign :: (Relation rel val, Eq val) => Var -> val -> UnionFind val rel -> Maybe (UnionFind val rel)
assign var value (UnionFind relations) =
  case IntMap.lookup var relations of
    -- The variable is not in the map, so we add it as a constant
    Nothing -> Just $ UnionFind $ IntMap.insert var (IsConstant value) relations
    -- The variable is already a constant, so we check if the value is the same
    Just (IsConstant oldValue) ->
      if oldValue == value
        then Nothing
        else error $ "[ panic ] Solver: trying to assign a different value to a constant variable: " <> show var
    -- The variable is already a root, so we:
    --    1. Make its children constants
    --    2. Make the root itself a constant
    Just (IsRoot toChildren) ->
      Just $
        UnionFind $
          foldl
            ( \rels (child, relationToChild) ->
                -- child = relationToChild var
                -- var = value
                --    =>
                -- child = relationToChild value
                IntMap.insert
                  child
                  (IsConstant (Relation.execute relationToChild value))
                  rels
            )
            (IntMap.insert var (IsConstant value) relations)
            (IntMap.toList toChildren)
    -- The variable is already a child of another variable, so we:
    --    1. Make the parent a constant (by calling `assign` recursively)
    -- child = relation parent
    -- =>
    -- parent = relation^-1 child
    Just (IsChildOf parent relationToChild) ->
      assign parent (Relation.execute (Relation.invert relationToChild) value) (UnionFind relations)

--------------------------------------------------------------------------------

-- | Relates two variables, using the more "senior" one as the root, if they have the same seniority, the one with the most children is used, O(lg n)
relate :: (Relation rel val, Eq val) => Var -> Var -> rel -> UnionFind val rel -> Maybe (UnionFind val rel)
relate a b relation relations = relateWithLookup (a, lookupStatus a relations) relation (b, lookupStatus b relations) relations

-- | Relates two variables, using the more "senior" one as the root, if they have the same seniority, the one with the most children is used, O(lg n)
relateWithLookup :: (Relation rel var, Eq var) => (Var, Status var rel) -> rel -> (Var, Status var rel) -> UnionFind var rel -> Maybe (UnionFind var rel)
relateWithLookup (a, aLookup) relation (b, bLookup) relations =
  if a == b -- if the variables are the same, do nothing and return the original relations
    then Nothing
    else case compareSeniority a b of
      LT -> relateChildToParent (a, aLookup) relation (b, bLookup) relations
      GT -> relateChildToParent (b, bLookup) (Relation.invert relation) (a, aLookup) relations
      EQ -> case compare (childrenSizeOf aLookup) (childrenSizeOf bLookup) of
        LT -> relateChildToParent (a, aLookup) relation (b, bLookup) relations
        GT -> relateChildToParent (b, bLookup) (Relation.invert relation) (a, aLookup) relations
        EQ -> relateChildToParent (a, aLookup) relation (b, bLookup) relations
        where
          childrenSizeOf :: Status val rel -> Int
          childrenSizeOf (IsRoot children) = IntMap.size children
          childrenSizeOf (IsConstant _) = 0
          childrenSizeOf (IsChildOf parent _) = childrenSizeOf (lookupStatus parent relations)

-- | Relates a child to a parent, O(lg n)
--   child = relation parent
relateChildToParent :: (Relation rel val, Eq val) => (Var, Status val rel) -> rel -> (Var, Status val rel) -> UnionFind val rel -> Maybe (UnionFind val rel)
relateChildToParent (child, childLookup) relationToChild (parent, parentLookup) relations = case parentLookup of
  -- The parent is a constant, so we make the child a constant:
  --    * for the parent: do nothing
  --    * for the child: assign it the value of the parent with `relationToChild` applied
  IsConstant value -> assign child (Relation.execute relationToChild value) relations
  -- The parent has other children
  IsRoot children -> case childLookup of
    -- The child also has its grandchildren, so we relate all these grandchildren to the parent, too:
    --    * for the parent: add the child and its grandchildren to the children map
    --    * for the child: point the child to the parent and add the relation
    --    * for the grandchildren: point them to the new parent
    IsRoot toGrandChildren ->
      let -- point the grandchildren to the new parent
          grandChildren =
            IntMap.foldlWithKey'
              (\rels grandchild relationToGrandChild -> IntMap.insert grandchild (IsChildOf parent (relationToGrandChild <> relationToChild)) rels)
              (unUnionFind relations)
              toGrandChildren
          newSiblings = IntMap.insert child relationToChild $ IntMap.map (<> relationToChild) toGrandChildren
       in Just $
            UnionFind $
              IntMap.insert parent (IsRoot (children <> newSiblings)) $ -- add the child and its grandchildren to the parent
                IntMap.insert
                  child
                  (IsChildOf parent relationToChild) -- add the child and its grandchildren to the parent
                  grandChildren
    -- The child is a constant, so we make the parent a constant, too:
    --  * for the parent: assign it the value of the child with the inverted relation applied
    --  * for the child: do nothing
    IsConstant value -> assign parent (Relation.execute (Relation.invert relationToChild) value) relations
    -- The child is already a child of another variable `parent2`:
    --    * for the another variable `parent2`: point `parent2` to `parent` with `Relation.invert parent2ToChild <> relationToChild`
    --    * for the parent: add the child and `parent2` to the children map
    --    * for the child: point it to the `parent` with `relationToParent`
    IsChildOf parent2 parent2ToChild ->
      if parent2 `compareSeniority` parent == GT
        then --
        -- child = relationToChild parent
        -- child = parent2ToChild parent2
        --    => parent = (Relation.invert relationToChild <> parent2ToChild) parent2
        --    or parent2 = (Relation.invert parent2ToChild <> relationToChild) parent
          relateWithLookup (parent, parentLookup) (Relation.invert relationToChild <> parent2ToChild) (parent2, lookupStatus parent2 relations) relations
        else do
          -- child = relationToChild parent
          -- child = parent2ToChild parent2
          --    => parent2 = (Relation.invert parent2ToChild <> relationToChild) parent
          --    or parent = (Relation.invert relationToChild <> parent2ToChild) parent2
          relateWithLookup (parent2, lookupStatus parent2 relations) (Relation.invert parent2ToChild <> relationToChild) (parent, parentLookup) $
            UnionFind $
              IntMap.insert child (IsChildOf parent relationToChild) $
                unUnionFind relations

  -- The parent is a child of another variable, so we relate the child to the grandparent instead
  IsChildOf grandparent relationFromGrandparent -> relateWithLookup (child, childLookup) (relationToChild <> relationFromGrandparent) (grandparent, lookupStatus grandparent relations) relations

--------------------------------------------------------------------------------

-- | Calculates the relation between two variables, O(lg n)
relationBetween :: (Relation rel val) => Var -> Var -> UnionFind val rel -> Maybe rel
relationBetween var1 var2 xs = case (lookupStatus var1 xs, lookupStatus var2 xs) of
  (IsConstant _, _) -> Nothing
  (_, IsConstant _) -> Nothing
  (IsRoot _, IsRoot _) ->
    if var1 == var2
      then Just mempty
      else Nothing
  (IsRoot _, IsChildOf parent2 relationWithParent2) ->
    if var1 == parent2
      then -- var2 = relationWithParent2 parent2
      -- var1 = parent2
      -- =>
      -- var2 = relationWithParent2 var1
        Just $ Relation.invert relationWithParent2
      else Nothing
  (IsChildOf parent1 relationWithParent1, IsRoot _) ->
    if parent1 == var2
      then -- var1 = relationWithParent1 parent1
      -- parent1 = var2
      -- =>
      -- var1 = relationWithParent1 var2
        Just relationWithParent1
      else Nothing
  (IsChildOf parent1 relationWithParent1, IsChildOf parent2 relationWithParent2) ->
    if parent1 == parent2
      then -- var1 = relationWithParent1 parent1
      -- var2 = relationWithParent2 parent2
      -- parent1 == parent2
      --   =>
      -- var1 = relationWithParent1 parent2
      -- var2 = relationWithParent2 parent2
        Just $ relationWithParent1 <> Relation.invert relationWithParent2
      else -- Just $ relationWithParent1 <> Relation.invert relationWithParent2
        Nothing

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
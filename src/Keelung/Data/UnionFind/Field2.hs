{-# HLINT ignore "Use list comprehension" #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Data.UnionFind.Field2
  ( -- * Construction

    -- UnionFind,
    -- new,

    -- * Operations

    -- assign,
    -- relate,

    -- * Conversions,

    -- export,
    -- renderFamilies,

    -- * Queries

    -- Lookup (..),
    -- lookup,
    -- relationBetween,
    -- size,

    -- * Linear Relations

    -- LinRel (..),
    -- invertLinRel,
    -- execLinRel,

    -- * Testing
    Error (..),
    validate,
    isValid,
  )
where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung (Var)
import Keelung.Compiler.Relations.Monad (Seniority (compareSeniority))
import Keelung.Data.Dict (Dict)
import Keelung.Data.Dict qualified as Dict
import Keelung.Data.UnionFind (UnionFind)
import Keelung.Data.UnionFind qualified as UnionFind
import Keelung.Data.UnionFind.Type
import Prelude hiding (lookup)

--------------------------------------------------------------------------------

instance (GaloisField n, Integral n) => UnionFind Var n where
  data Map Var n = FieldIntMap
    { unFieldIntMap :: Dict Var (VarStatus Var n) -- relation of each variable
    }
    deriving (Eq, Generic)

  -- Relation representing a linear function between two variables, i.e. x = ay + b
  data Rel n
    = LinRel
        n -- slope
        n -- intercept
    deriving (Show, Eq, Generic, Functor, NFData)

  new = FieldIntMap mempty
  assign = assign
  relate = relate
  lookup = lookup
  export = export

-- instance (Serialize n) => Serialize (UnionFind.Map Var n)

instance (GaloisField n, Integral n) => Show (UnionFind.Map Var n) where
  show (FieldIntMap relations) =
    "Field IntMap UnionFind\n"
      <> mconcat (map (<> "\n") (concatMap toString (Dict.toList relations)))
    where
      showVar var = let varString = "$" <> show var in "  " <> varString <> replicate (8 - length varString) ' '

      toString (var, IsConstant value) = [showVar var <> " = " <> show value]
      toString (var, IsRoot toChildren) = case map renderLinRel (Dict.toList toChildren) of
        [] -> [showVar var <> " = []"] -- should never happen
        (x : xs) -> showVar var <> " = " <> x : map ("           = " <>) xs
      toString (_var, IsChildOf _parent _relation) = []

--------------------------------------------------------------------------------

-- | Assigns a value to a variable, O(lg n)
assign :: (GaloisField n, Integral n) => Var -> n -> UnionFind.Map Var n -> Maybe (UnionFind.Map Var n)
assign var value (FieldIntMap relations) =
  case Dict.lookup var relations of
    -- The variable is not in the map, so we add it as a constant
    Nothing -> Just $ FieldIntMap $ Dict.insert var (IsConstant value) relations
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
        FieldIntMap $
          foldl
            ( \rels (child, relationToChild) ->
                -- child = relationToChild var
                -- var = value
                --    =>
                -- child = relationToChild value
                Dict.insert
                  child
                  (IsConstant (execLinRel relationToChild value))
                  rels
            )
            (Dict.insert var (IsConstant value) relations)
            (Dict.toList toChildren)
    -- The variable is already a child of another variable, so we:
    --    1. Make the parent a constant (by calling `assign` recursively)
    -- child = relation parent
    -- =>
    -- parent = relation^-1 child
    Just (IsChildOf parent relationToChild) ->
      assign parent (execLinRel (invertLinRel relationToChild) value) (FieldIntMap relations)

-- | Relates two variables, using the more "senior" one as the root, if they have the same seniority, the one with the most children is used, O(lg n)
relate :: (GaloisField n, Integral n) => Var -> Var -> UnionFind.Rel n -> UnionFind.Map Var n -> Maybe (UnionFind.Map Var n)
relate a b relation relations = relateWithLookup (a, lookupInternal a relations) relation (b, lookupInternal b relations) relations

-- | Relates two variables, using the more "senior" one as the root, if they have the same seniority, the one with the most children is used, O(lg n)
relateWithLookup :: (GaloisField n, Integral n) => (Var, VarStatus Var n) -> UnionFind.Rel n -> (Var, VarStatus Var n) -> UnionFind.Map Var n -> Maybe (UnionFind.Map Var n)
relateWithLookup (a, aLookup) relation (b, bLookup) relations =
  if a == b -- if the variables are the same, do nothing and return the original relations
    then Nothing
    else case compareSeniority a b of
      LT -> relateChildToParent (a, aLookup) relation (b, bLookup) relations
      GT -> relateChildToParent (b, bLookup) (invertLinRel relation) (a, aLookup) relations
      EQ -> case compare (childrenSizeOf aLookup) (childrenSizeOf bLookup) of
        LT -> relateChildToParent (a, aLookup) relation (b, bLookup) relations
        GT -> relateChildToParent (b, bLookup) (invertLinRel relation) (a, aLookup) relations
        EQ -> relateChildToParent (a, aLookup) relation (b, bLookup) relations
        where
          childrenSizeOf :: VarStatus Var n -> Int
          childrenSizeOf (IsRoot children) = Dict.size children
          childrenSizeOf (IsConstant _) = 0
          childrenSizeOf (IsChildOf parent _) = childrenSizeOf (lookupInternal parent relations)

-- | Relates a child to a parent, O(lg n)
--   child = relation parent
relateChildToParent :: (GaloisField n, Integral n) => (Var, VarStatus Var n) -> UnionFind.Rel n -> (Var, VarStatus Var n) -> UnionFind.Map Var n -> Maybe (UnionFind.Map Var n)
relateChildToParent (child, childLookup) relationToChild (parent, parentLookup) relations = case parentLookup of
  -- The parent is a constant, so we make the child a constant:
  --    * for the parent: do nothing
  --    * for the child: assign it the value of the parent with `relationToChild` applied
  IsConstant value -> assign child (execLinRel relationToChild value) relations
  -- The parent has other children
  IsRoot children -> case childLookup of
    -- The child also has its grandchildren, so we relate all these grandchildren to the parent, too:
    --    * for the parent: add the child and its grandchildren to the children map
    --    * for the child: point the child to the parent and add the relation
    --    * for the grandchildren: point them to the new parent
    IsRoot toGrandChildren ->
      let -- point the grandchildren to the new parent
          grandChildren =
            Dict.foldlWithKey
              (\rels grandchild relationToGrandChild -> Dict.insert grandchild (IsChildOf parent (relationToGrandChild <> relationToChild)) rels)
              (unFieldIntMap relations)
              toGrandChildren
          newSiblings = Dict.insert child relationToChild $ fmap (<> relationToChild) toGrandChildren
       in Just $
            FieldIntMap $
              Dict.insert parent (IsRoot (children <> newSiblings)) $ -- add the child and its grandchildren to the parent
                Dict.insert
                  child
                  (IsChildOf parent relationToChild) -- add the child and its grandchildren to the parent
                  grandChildren
    -- The child is a constant, so we make the parent a constant, too:
    --  * for the parent: assign it the value of the child with the inverted relation applied
    --  * for the child: do nothing
    IsConstant value -> assign parent (execLinRel (invertLinRel relationToChild) value) relations
    -- The child is already a child of another variable `parent2`:
    --    * for the another variable `parent2`: point `parent2` to `parent` with `invertLinRel parent2ToChild <> relationToChild`
    --    * for the parent: add the child and `parent2` to the children map
    --    * for the child: point it to the `parent` with `relationToParent`
    IsChildOf parent2 parent2ToChild ->
      if parent2 `compareSeniority` parent == GT
        then --
        -- child = relationToChild parent
        -- child = parent2ToChild parent2
        --    => parent = (invertLinRel relationToChild <> parent2ToChild) parent2
        --    or parent2 = (invertLinRel parent2ToChild <> relationToChild) parent
          relateWithLookup (parent, parentLookup) (invertLinRel relationToChild <> parent2ToChild) (parent2, lookupInternal parent2 relations) relations
        else do
          -- child = relationToChild parent
          -- child = parent2ToChild parent2
          --    => parent2 = (invertLinRel parent2ToChild <> relationToChild) parent
          --    or parent = (invertLinRel relationToChild <> parent2ToChild) parent2
          relateWithLookup (parent2, lookupInternal parent2 relations) (invertLinRel parent2ToChild <> relationToChild) (parent, parentLookup) $
            FieldIntMap $
              Dict.insert child (IsChildOf parent relationToChild) $
                unFieldIntMap relations

  -- The parent is a child of another variable, so we relate the child to the grandparent instead
  IsChildOf grandparent relationFromGrandparent -> relateWithLookup (child, childLookup) (relationToChild <> relationFromGrandparent) (grandparent, lookupInternal grandparent relations) relations

--------------------------------------------------------------------------------

-- | Exports the UnionFind as a pair of:
--    1. a map from the constant variables to their values
--    2. a map from the root variables to their children with the relation `(slope, intercept)`
export ::
  UnionFind.Map Var n ->
  ( Dict Var n, -- constants
    Dict Var (Dict Var (UnionFind.Rel n)) -- families
  )
export (FieldIntMap relations) = (constants, roots)
  where
    constants = Dict.mapMaybe toConstant relations
    roots = Dict.mapMaybe toRoot relations

    toConstant (IsConstant value) = Just value
    toConstant _ = Nothing

    toRoot (IsRoot children) = Just children
    toRoot _ = Nothing

-- --------------------------------------------------------------------------------

-- -- | Calculates the relation between two variables, O(lg n)
-- relationBetween :: (GaloisField n, Integral n) => Var -> Var -> UnionFind n -> Maybe (n, n)
-- relationBetween var1 var2 xs =
--   fromLinRel <$> case (lookupInternal var1 xs, lookupInternal var2 xs) of
--     (IsConstant _, _) -> Nothing
--     (_, IsConstant _) -> Nothing
--     (IsRoot _, IsRoot _) ->
--       if var1 == var2
--         then Just mempty
--         else Nothing
--     (IsRoot _, IsChildOf parent2 relationWithParent2) ->
--       if var1 == parent2
--         then -- var2 = relationWithParent2 parent2
--         -- var1 = parent2
--         -- =>
--         -- var2 = relationWithParent2 var1
--           Just $ invertLinRel relationWithParent2
--         else Nothing
--     (IsChildOf parent1 relationWithParent1, IsRoot _) ->
--       if parent1 == var2
--         then -- var1 = relationWithParent1 parent1
--         -- parent1 = var2
--         -- =>
--         -- var1 = relationWithParent1 var2
--           Just relationWithParent1
--         else Nothing
--     (IsChildOf parent1 relationWithParent1, IsChildOf parent2 relationWithParent2) ->
--       if parent1 == parent2
--         then -- var1 = relationWithParent1 parent1
--         -- var2 = relationWithParent2 parent2
--         -- parent1 == parent2
--         --   =>
--         -- var1 = relationWithParent1 parent2
--         -- var2 = relationWithParent2 parent2
--           Just $ relationWithParent1 <> invertLinRel relationWithParent2
--         else -- Just $ relationWithParent1 <> invertLinRel relationWithParent2
--           Nothing

-- -- | Returns the number of variables in the Reference, O(1)
-- size :: UnionFind n -> Int
-- size = IntMap.size . unFieldIntMap

--------------------------------------------------------------------------------

data VarStatus var n
  = IsConstant n
  | IsRoot
      (Dict var (UnionFind.Rel n)) -- mappping from the child to the relation
  | IsChildOf
      Var -- parent
      (UnionFind.Rel n) -- relation such that `child = relation parent`
  deriving (Generic)

instance (Eq n, Eq (Dict var (UnionFind.Rel n))) => Eq (VarStatus var n) where
  IsConstant a == IsConstant b = a == b
  IsRoot a == IsRoot b = a == b
  IsChildOf a b == IsChildOf c d = a == c && b == d
  _ == _ = False

instance (Show n, Show (Dict var (UnionFind.Rel n))) => Show (VarStatus var n) where
  show (IsConstant value) = "IsConstant " <> show value
  show (IsRoot children) = "IsRoot " <> show children
  show (IsChildOf parent relation) = "IsChildOf " <> show parent <> " " <> show relation

-- instance (NFData n) => NFData (VarStatus var n)

-- instance (Serialize n) => Serialize (VarStatus var n)

-- | Returns the result of looking up a variable, O(lg n)
lookupInternal :: Var -> UnionFind.Map Var n -> VarStatus Var n
lookupInternal var (FieldIntMap relations) = case Dict.lookup var relations of
  Nothing -> IsRoot mempty
  Just result -> result

--------------------------------------------------------------------------------

-- | Result of looking up a variable in the Relations
lookup :: (GaloisField n) => Var -> UnionFind.Map Var n -> Lookup Var n (UnionFind.Rel n)
lookup var relations =
  case lookupInternal var relations of
    IsConstant value -> Constant value
    IsRoot _ -> Root
    IsChildOf parent relation -> ChildOf parent relation

--------------------------------------------------------------------------------

-- data LinRel n
--   = LinRel
--       n -- slope
--       n -- intercept
--   deriving (Show, Eq, NFData, Generic, Functor)

-- | x ~a~ y & y ~b~ z => x ~a<>b~ z
instance (Num n) => Semigroup (UnionFind.Rel n) where
  -- x = a1 * y + b1
  -- y = a2 * z + b2
  -- =>
  -- x = a1 * (a2 * z + b2) + b1
  --   = (a1 * a2) * z + (a1 * b2 + b1)
  LinRel a1 b1 <> LinRel a2 b2 = LinRel (a1 * a2) (a1 * b2 + b1)

instance (Num n) => Monoid (UnionFind.Rel n) where
  mempty = LinRel 1 0

instance (Serialize n) => Serialize (UnionFind.Rel n)

-- | Computes the inverse of a relation
--      x = ay + b
--        =>
--      y = (1/a) x + (-b/a)
invertLinRel :: (GaloisField n, Integral n) => UnionFind.Rel n -> UnionFind.Rel n
invertLinRel (LinRel a b) = LinRel (recip a) ((-b) / a)

-- | `execLinRel relation parent = child`
execLinRel :: (GaloisField n, Integral n) => UnionFind.Rel n -> n -> n
execLinRel (LinRel a b) value = a * value + b

-- | Render LinRel to some child as a string
renderLinRel :: (GaloisField n, Integral n) => (Int, UnionFind.Rel n) -> String
renderLinRel (var, rel) = go (invertLinRel rel)
  where
    var' = "$" <> show var

    go (LinRel (-1) 1) = "¬" <> var'
    go (LinRel a b) =
      let slope = case a of
            1 -> var'
            (-1) -> "-" <> var'
            _ -> show a <> var'
          intercept = case b of
            0 -> ""
            _ -> " + " <> show b
       in -- if N.isPositive b
          --   then " + " <> show (N b)
          --   else " - " <> show (N (-b))
          slope <> intercept

--------------------------------------------------------------------------------

-- | For testing the validity of the data structure
data Error key
  = RootNotSenior Var [key]
  | ChildrenNotRecognizingParent Var [key]
  deriving (Show, Eq)

-- | The data structure is valid if:
--    1. all children of a parent recognize the parent as their parent
--    2. the seniority of the root of a family is greater than equal the seniority of all its children
validate :: (GaloisField n, Integral n) => UnionFind.Map Var n -> [Error Var]
validate relations = allChildrenRecognizeTheirParent relations <> rootsAreSenior relations

-- | Derived from `validate`
isValid :: (GaloisField n, Integral n) => UnionFind.Map Var n -> Bool
isValid = null . validate

-- | A Reference is valid if all children of a parent recognize the parent as their parent
allChildrenRecognizeTheirParent :: (GaloisField n, Integral n) => UnionFind.Map Var n -> [Error Var]
allChildrenRecognizeTheirParent relations =
  let families = Dict.mapMaybe isParent (unFieldIntMap relations)

      isParent (IsRoot children) = Just children
      isParent _ = Nothing

      recognizeParent parent child relation = case lookupInternal child relations of
        IsChildOf parent' relation' -> parent == parent' && relation == relation'
        _ -> False
      childrenNotRecognizeParent parent = Dict.filterWithKey (\child status -> not $ recognizeParent parent child status)
   in --  . IntMap.elems . IntMap.mapWithKey (recognizeParent parent)
      concatMap
        ( \(parent, children) ->
            let badChildren = childrenNotRecognizeParent parent children
             in if null badChildren then [] else [ChildrenNotRecognizingParent parent (Dict.keys badChildren)]
        )
        $ Dict.toList families

-- | A Reference is valid if the seniority of the root of a family is greater than equal the seniority of all its children
rootsAreSenior :: UnionFind.Map Var n -> [Error Var]
rootsAreSenior = Dict.foldlWithKey go [] . unFieldIntMap
  where
    go :: [Error Var] -> Var -> VarStatus Var n -> [Error Var]
    go acc _ (IsConstant _) = acc
    go acc var (IsRoot children) =
      let badChildren = filter (\child -> compareSeniority var child == LT) (Dict.keys children)
       in if null badChildren then acc else RootNotSenior var badChildren : acc
    go acc var (IsChildOf parent _) = if compareSeniority parent var /= LT then acc else RootNotSenior parent [var] : acc
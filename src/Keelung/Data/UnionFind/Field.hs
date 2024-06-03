{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use list comprehension" #-}

module Keelung.Data.UnionFind.Field
  ( -- * Construction
    UnionFind,
    new,

    -- * Operations
    assign,
    relate,

    -- * Conversions,
    export,
    renderFamilies,

    -- * Queries
    Lookup (..),
    lookup,
    relationBetween,
    size,

    -- * Linear Relations
    LinRel (..),
    invertLinRel,
    execLinRel,

    -- * Testing
    Error (..),
    validate,
    isValid,
  )
where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung (N (N), Var)
import Keelung.Compiler.Relations.Monad (Seniority (compareSeniority))
import Keelung.Data.N qualified as N
import Prelude hiding (lookup)

--------------------------------------------------------------------------------

newtype UnionFind n = UnionFind {unUnionFind :: IntMap (VarStatus n)} -- relation to the parent
  deriving (Eq, Generic, Functor)

instance (Serialize n) => Serialize (UnionFind n)

instance (GaloisField n, Integral n) => Show (UnionFind n) where
  show (UnionFind relations) =
    "UnionFind\n"
      <> mconcat (map (<> "\n") (concatMap toString (IntMap.toList relations)))
    where
      showVar var = let varString = "$" <> show var in "  " <> varString <> replicate (8 - length varString) ' '

      toString (var, IsConstant value) = [showVar var <> " = " <> show value]
      toString (var, IsRoot toChildren) = case map renderLinRel (IntMap.toList toChildren) of
        [] -> [showVar var <> " = []"] -- should never happen
        (x : xs) -> showVar var <> " = " <> x : map ("           = " <>) xs
      toString (_var, IsChildOf _parent _relation) = []

instance (NFData n) => NFData (UnionFind n)

-- | Creates a new UnionFind, O(1)
new :: UnionFind n
new = UnionFind mempty

--------------------------------------------------------------------------------

-- | Assigns a value to a variable, O(lg n)
assign :: (GaloisField n, Integral n) => Var -> n -> UnionFind n -> Maybe (UnionFind n)
assign var value (UnionFind relations) = case IntMap.lookup var relations of
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
                (IsConstant (execLinRel relationToChild value))
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
    assign parent (execLinRel (invertLinRel relationToChild) value) (UnionFind relations)

-- | Relates two variables, using the more "senior" one as the root, if they have the same seniority, the one with the most children is used, O(lg n)
relate :: (GaloisField n, Integral n) => Var -> n -> Var -> n -> UnionFind n -> Maybe (UnionFind n)
relate a slope b intercept relations = relateWithLookup (a, lookupInternal a relations) (LinRel slope intercept) (b, lookupInternal b relations) relations

-- | Relates two variables, using the more "senior" one as the root, if they have the same seniority, the one with the most children is used, O(lg n)
relateWithLookup :: (GaloisField n, Integral n) => (Var, VarStatus n) -> LinRel n -> (Var, VarStatus n) -> UnionFind n -> Maybe (UnionFind n)
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
          childrenSizeOf :: VarStatus n -> Int
          childrenSizeOf (IsRoot children) = IntMap.size children
          childrenSizeOf (IsConstant _) = 0
          childrenSizeOf (IsChildOf parent _) = childrenSizeOf (lookupInternal parent relations)

-- | Relates a child to a parent, O(lg n)
--   child = relation parent
relateChildToParent :: (GaloisField n, Integral n) => (Var, VarStatus n) -> LinRel n -> (Var, VarStatus n) -> UnionFind n -> Maybe (UnionFind n)
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
      let newSiblings = IntMap.insert child relationToChild $ IntMap.map (relationToChild <>) toGrandChildren
       in Just $
            UnionFind $
              IntMap.insert parent (IsRoot (children <> newSiblings)) $
                IntMap.insert child (IsChildOf parent relationToChild) $ -- add the child and its grandchildren to the parent
                -- add the child and its grandchildren to the parent
                  IntMap.foldlWithKey' -- point the child to the parent
                  -- point the grandchildren to the new parent
                    (\rels grandchild relationToGrandChild -> IntMap.insert grandchild (IsChildOf parent (relationToChild <> relationToGrandChild)) rels)
                    (unUnionFind relations)
                    toGrandChildren
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
            UnionFind $
              IntMap.insert child (IsChildOf parent relationToChild) $
                unUnionFind relations

  -- The parent is a child of another variable, so we relate the child to the grandparent instead
  IsChildOf grandparent relationFromGrandparent -> relateWithLookup (child, childLookup) (relationToChild <> relationFromGrandparent) (grandparent, lookupInternal grandparent relations) relations

--------------------------------------------------------------------------------

-- | Exports the UnionFind as a pair of:
--    1. a map from the constant variables to their values
--    2. a map from the root variables to their children with the relation `(slope, intercept)`
export ::
  UnionFind n ->
  ( IntMap n, -- constants
    IntMap (IntMap (n, n)) -- families
  )
export (UnionFind relations) = (constants, roots)
  where
    constants = IntMap.mapMaybe toConstant relations
    roots = IntMap.mapMaybe toRoot relations

    toConstant (IsConstant value) = Just value
    toConstant _ = Nothing

    toRoot (IsRoot children) = Just $ IntMap.map fromLinRel children
    toRoot _ = Nothing

-- | Helper function to render the families resulted from `export`
renderFamilies :: (GaloisField n, Integral n) => IntMap (IntMap (n, n)) -> String
renderFamilies families = mconcat (map (<> "\n") (concatMap toString (IntMap.toList families)))
  where
    showVar var = let varString = "$" <> show var in "  " <> varString <> replicate (8 - length varString) ' '
    toString (root, toChildren) = case map renderLinRel (IntMap.toList (fmap (uncurry LinRel) toChildren)) of
      [] -> [showVar root <> " = []"] -- should never happen
      (x : xs) -> showVar root <> " = " <> x : map ("           = " <>) xs

--------------------------------------------------------------------------------

-- | Calculates the relation between two variables, O(lg n)
relationBetween :: (GaloisField n, Integral n) => Var -> Var -> UnionFind n -> Maybe (n, n)
relationBetween var1 var2 xs =
  fromLinRel <$> case (lookupInternal var1 xs, lookupInternal var2 xs) of
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
          Just $ invertLinRel relationWithParent2
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
          Just $ relationWithParent1 <> invertLinRel relationWithParent2
        else -- Just $ relationWithParent1 <> invertLinRel relationWithParent2
          Nothing

-- | Returns the number of variables in the Reference, O(1)
size :: UnionFind n -> Int
size = IntMap.size . unUnionFind

--------------------------------------------------------------------------------

data VarStatus n
  = IsConstant n
  | IsRoot
      (IntMap (LinRel n)) -- mappping from the child to the relation
  | IsChildOf
      Var -- parent
      (LinRel n) -- relation such that `child = relation parent`
  deriving (Show, Eq, Generic, Functor)

instance (NFData n) => NFData (VarStatus n)

instance (Serialize n) => Serialize (VarStatus n)

-- | Returns the result of looking up a variable, O(lg n)
lookupInternal :: Var -> UnionFind n -> VarStatus n
lookupInternal var (UnionFind relations) = case IntMap.lookup var relations of
  Nothing -> IsRoot mempty
  Just result -> result

--------------------------------------------------------------------------------

-- | Result of looking up a variable in the Relations
data Lookup n = Root | Constant n | ChildOf n Var n
  deriving (Eq, Show)

lookup :: (GaloisField n) => Var -> UnionFind n -> Lookup n
lookup var relations =
  case lookupInternal var relations of
    IsConstant value -> Constant value
    IsRoot _ -> Root
    IsChildOf parent (LinRel a b) -> ChildOf a parent b

--------------------------------------------------------------------------------

-- | Relation representing a linear function between two variables, i.e. x = ay + b
data LinRel n
  = LinRel
      n -- slope
      n -- intercept
  deriving (Show, Eq, NFData, Generic, Functor)

instance (Num n) => Semigroup (LinRel n) where
  -- x = a1 * y + b1
  -- y = a2 * z + b2
  -- =>
  -- x = a1 * (a2 * z + b2) + b1
  --   = (a1 * a2) * z + (a1 * b2 + b1)
  LinRel a1 b1 <> LinRel a2 b2 = LinRel (a1 * a2) (a1 * b2 + b1)

instance (Num n) => Monoid (LinRel n) where
  mempty = LinRel 1 0

instance (Serialize n) => Serialize (LinRel n)

-- | Extracts the coefficients from a LinRel
fromLinRel :: LinRel n -> (n, n)
fromLinRel (LinRel a b) = (a, b)

-- | Computes the inverse of a relation
--      x = ay + b
--        =>
--      y = (1/a) x + (-b/a)
invertLinRel :: (GaloisField n, Integral n) => LinRel n -> LinRel n
invertLinRel (LinRel a b) = LinRel (recip a) ((-b) / a)

-- | `execLinRel relation parent = child`
execLinRel :: (GaloisField n, Integral n) => LinRel n -> n -> n
execLinRel (LinRel a b) value = a * value + b

-- | Render LinRel to some child as a string
renderLinRel :: (GaloisField n, Integral n) => (Int, LinRel n) -> String
renderLinRel (var, rel) = go rel
  where
    var' = "$" <> show var

    go (LinRel (-1) 1) = "¬" <> var'
    go (LinRel a b) =
      let slope = case a of
            1 -> var'
            (-1) -> "-" <> var'
            _ -> show (N a) <> var'
          intercept = case b of
            0 -> ""
            _ ->
              if N.isPositive b
                then " + " <> show (N b)
                else " - " <> show (N (-b))
       in slope <> intercept

--------------------------------------------------------------------------------

-- | For testing the validity of the data structure
data Error
  = RootNotSenior Var IntSet
  | ChildrenNotRecognizingParent Var IntSet
  deriving (Show, Eq)

-- | The data structure is valid if:
--    1. all children of a parent recognize the parent as their parent
--    2. the seniority of the root of a family is greater than equal the seniority of all its children
validate :: (GaloisField n, Integral n) => UnionFind n -> [Error]
validate relations = allChildrenRecognizeTheirParent relations <> rootsAreSenior relations

-- | Derived from `validate`
isValid :: (GaloisField n, Integral n) => UnionFind n -> Bool
isValid = null . validate

-- | A Reference is valid if all children of a parent recognize the parent as their parent
allChildrenRecognizeTheirParent :: (GaloisField n, Integral n) => UnionFind n -> [Error]
allChildrenRecognizeTheirParent relations =
  let families = IntMap.mapMaybe isParent (unUnionFind relations)

      isParent (IsRoot children) = Just children
      isParent _ = Nothing

      recognizeParent parent child relation = case lookupInternal child relations of
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
rootsAreSenior :: UnionFind n -> [Error]
rootsAreSenior = IntMap.foldlWithKey' go [] . unUnionFind
  where
    go :: [Error] -> Var -> VarStatus n -> [Error]
    go acc _ (IsConstant _) = acc
    go acc var (IsRoot children) =
      let badChildren = IntSet.filter (\child -> compareSeniority var child == LT) (IntMap.keysSet children)
       in if IntSet.null badChildren then acc else RootNotSenior var badChildren : acc
    go acc var (IsChildOf parent _) = if compareSeniority parent var /= LT then acc else RootNotSenior parent (IntSet.singleton var) : acc
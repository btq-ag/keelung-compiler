{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Relations.Reference
  ( RefRelations,

    -- * Construction
    new,

    -- * Operations
    assign,
    relate,
    relateB,

    -- * Conversions,
    toConstraints,

    -- * Queries
    Lookup (..),
    lookup,
    relationBetween,
    size,
    isValid,
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Control.Monad.Writer
import Data.Field.Galois (Binary, GaloisField, Prime)
import Data.Foldable (toList)
import Data.Map qualified as Map
import Data.Map.Strict (Map)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import GHC.Generics (Generic)
import GHC.TypeLits
import Keelung.Compiler.Compile.Error (Error (..))
import Keelung.Compiler.Relations.Monad
import Keelung.Compiler.Relations.Slice (SliceRelations)
import Keelung.Compiler.Relations.Slice qualified as SliceRelations
import Keelung.Data.Constraint (Constraint (..))
import Keelung.Data.N (N (..))
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Prelude hiding (lookup)

--------------------------------------------------------------------------------

newtype RefRelations n = RefRelations {unRefRelations :: Map Ref (VarStatus n)} -- relation to the parent
  deriving (Eq, Generic, Functor)

instance (NFData n) => NFData (RefRelations n)

-- | Instance for pretty-printing RefRelations with Galois fields as constant values
instance {-# OVERLAPS #-} (KnownNat n) => Show (RefRelations (Prime n)) where
  show (RefRelations refRels) =
    "Reference Relations\n"
      <> mconcat (map (<> "\n") (concatMap toString (Map.toList refRels)))
    where
      showVar var = let varString = show var in "  " <> varString <> replicate (8 - length varString) ' '

      toString (var, IsConstant value) = [showVar var <> " = " <> show (N value)]
      toString (var, IsRoot toChildren) = case map renderLinRel (Map.toList $ Map.mapKeys show toChildren) of
        [] -> [showVar var <> " = []"] -- should never happen
        (x : xs) -> showVar var <> " = " <> x : map ("           = " <>) xs
      toString (_var, IsChildOf _parent _relation) = []

-- | Instance for pretty-printing RefRelations with Galois fields as constant values
instance {-# OVERLAPPING #-} (KnownNat n) => Show (RefRelations (Binary n)) where
  show (RefRelations refRels) =
    "Reference Relations\n"
      <> mconcat (map (<> "\n") (concatMap toString (Map.toList refRels)))
    where
      showVar var = let varString = show var in "  " <> varString <> replicate (8 - length varString) ' '

      toString (var, IsConstant value) = [showVar var <> " = " <> show (N value)]
      toString (var, IsRoot toChildren) = case map renderLinRel (Map.toList $ Map.mapKeys show toChildren) of
        [] -> [showVar var <> " = []"]
        (x : xs) -> showVar var <> " = " <> x : map ("           = " <>) xs
      toString (_var, IsChildOf _parent _relation) = []

instance (GaloisField n, Integral n) => Show (RefRelations n) where
  show (RefRelations refRels) =
    "Reference Relations\n"
      <> mconcat (map (<> "\n") (concatMap toString (Map.toList refRels)))
    where
      showVar var = let varString = show var in "  " <> varString <> replicate (8 - length varString) ' '

      toString (var, IsConstant value) = [showVar var <> " = " <> show value]
      toString (var, IsRoot toChildren) = case map renderLinRel (Map.toList $ Map.mapKeys show toChildren) of
        [] -> [showVar var <> " = []"] -- should never happen
        (x : xs) -> showVar var <> " = " <> x : map ("           = " <>) xs
      toString (_var, IsChildOf _parent _relation) = []

-- | Creates a new RefRelations, O(1)
new :: RefRelations n
new = RefRelations mempty

--------------------------------------------------------------------------------

-- | Assigns a value to a variable, O(lg n)
assign :: (GaloisField n, Integral n) => Ref -> n -> RefRelations n -> SliceRelations -> RelM n (Maybe (RefRelations n))
assign var value (RefRelations refRels) sliceRels = case Map.lookup var refRels of
  -- The variable is not in the map, so we add it as a constant
  Nothing -> return $ Just $ RefRelations $ Map.insert var (IsConstant value) refRels
  -- The variable is already a constant, so we check if the value is the same
  Just (IsConstant oldValue) ->
    if oldValue == value
      then return Nothing
      else throwError (ConflictingValuesF oldValue value)
  -- The variable is already a root, so we:
  --    1. Make its children constants
  --    2. Make the root itself a constant
  Just (IsRoot toChildren) ->
    return $
      Just $
        RefRelations $
          foldl
            ( \rels (child, relationToChild) ->
                -- child = relationToChild var
                -- var = value
                --    =>
                -- child = relationToChild value
                Map.insert
                  child
                  (IsConstant (execLinRel relationToChild value))
                  rels
            )
            (Map.insert var (IsConstant value) refRels)
            (Map.toList toChildren)
  -- The variable is already a child of another variable, so we:
  --    1. Make the parent a constant (by calling `assign` recursively)
  -- child = relation parent
  -- =>
  -- parent = relation^-1 child
  Just (IsChildOf parent relationToChild) -> assign parent (execLinRel (invertLinRel relationToChild) value) (RefRelations refRels) sliceRels

-- | Relates two variables, using the more "senior" one as the root, if they have the same seniority, the one with the most children is used, O(lg n)
relateWithLinRel :: (GaloisField n, Integral n) => Ref -> LinRel n -> Ref -> RefRelations n -> SliceRelations -> RelM n (Maybe (RefRelations n))
relateWithLinRel a relation b refRels sliceRels = relateWithLookup (a, lookupInternal a refRels sliceRels) relation (b, lookupInternal b refRels sliceRels) refRels sliceRels

-- | Relates two variables, using the more "senior" one as the root, if they have the same seniority, the one with the most children is used, O(lg n)
relateWithLookup :: (GaloisField n, Integral n) => (Ref, VarStatus n) -> LinRel n -> (Ref, VarStatus n) -> RefRelations n -> SliceRelations -> RelM n (Maybe (RefRelations n))
relateWithLookup (a, aLookup) relation (b, bLookup) refRels sliceRels =
  if a == b -- if the variables are the same, do nothing and return the original relations
    then return Nothing
    else case compareSeniority a b of
      LT -> relateChildToParent (a, aLookup) relation (b, bLookup) refRels sliceRels
      GT -> relateChildToParent (b, bLookup) (invertLinRel relation) (a, aLookup) refRels sliceRels
      EQ -> case compare (childrenSizeOf aLookup) (childrenSizeOf bLookup) of
        LT -> relateChildToParent (a, aLookup) relation (b, bLookup) refRels sliceRels
        GT -> relateChildToParent (b, bLookup) (invertLinRel relation) (a, aLookup) refRels sliceRels
        EQ -> relateChildToParent (a, aLookup) relation (b, bLookup) refRels sliceRels
        where
          childrenSizeOf :: VarStatus n -> Int
          childrenSizeOf (IsRoot children) = Map.size children
          childrenSizeOf (IsConstant _) = 0
          childrenSizeOf (IsChildOf parent _) = childrenSizeOf (lookupInternal parent refRels sliceRels)

-- | Specialized version of `relateWithLinRel` for relating a variable to a constant
--    var = slope * var2 + intercept
relate :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> RefRelations n -> SliceRelations -> RelM n (Maybe (RefRelations n))
relate x slope y intercept = relateWithLinRel x (LinRel slope intercept) y

-- | Specialized version of `relateWithLinRel` for relating Boolean variables
relateB :: (GaloisField n, Integral n) => RefB -> (Bool, RefB) -> RefRelations n -> SliceRelations -> RelM n (Maybe (RefRelations n))
relateB refA (polarity, refB) = relateWithLinRel (B refA) (if polarity then LinRel 1 0 else LinRel (-1) 1) (B refB)

-- | Relates a child to a parent, O(lg n)
--   child = relation parent
relateChildToParent :: (GaloisField n, Integral n) => (Ref, VarStatus n) -> LinRel n -> (Ref, VarStatus n) -> RefRelations n -> SliceRelations -> RelM n (Maybe (RefRelations n))
relateChildToParent (child, childLookup) relationToChild (parent, parentLookup) refRels sliceRels =
  if child == parent
    then return Nothing -- no-op
    else case parentLookup of
      -- The parent is a constant, so we make the child a constant:
      --    * for the parent: do nothing
      --    * for the child: assign it the value of the parent with `relationToChild` applied
      IsConstant value -> assign child (execLinRel relationToChild value) refRels sliceRels
      -- The parent has other children
      IsRoot children -> case childLookup of
        -- The child also has its grandchildren, so we relate all these grandchildren to the parent, too:
        --    * for the parent: add the child and its grandchildren to the children map
        --    * for the child: point the child to the parent and add the relation
        --    * for the grandchildren: point them to the new parent
        IsRoot toGrandChildren -> do
          let newSiblings = Map.insert child relationToChild $ Map.map (relationToChild <>) toGrandChildren
          return $
            Just $
              RefRelations $
                Map.insert parent (IsRoot (children <> newSiblings)) $ -- add the child and its grandchildren to the parent
                -- add the child and its grandchildren to the parent
                  Map.insert child (IsChildOf parent relationToChild) $ -- point the child to the parent
                    Map.foldlWithKey' -- point the grandchildren to the new parent
                      ( \rels grandchild relationToGrandChild -> Map.insert grandchild (IsChildOf parent (relationToChild <> relationToGrandChild)) rels
                      )
                      (unRefRelations refRels)
                      toGrandChildren
        --
        -- The child is a constant, so we make the parent a constant, too:
        --  * for the parent: assign it the value of the child with the inverted relation applied
        --  * for the child: do nothing
        IsConstant value -> assign parent (execLinRel (invertLinRel relationToChild) value) refRels sliceRels
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
              relateWithLookup (parent, parentLookup) (invertLinRel relationToChild <> parent2ToChild) (parent2, lookupInternal parent2 refRels sliceRels) refRels sliceRels
            else do
              --
              -- child = relationToChild parent
              -- child = parent2ToChild parent2
              --    => parent2 = (invertLinRel parent2ToChild <> relationToChild) parent
              --    or parent = (invertLinRel relationToChild <> parent2ToChild) parent2
              relateWithLookup (parent2, lookupInternal parent2 refRels sliceRels) (invertLinRel parent2ToChild <> relationToChild) (parent, parentLookup)
                (RefRelations $
                  Map.insert child (IsChildOf parent relationToChild) $
                    unRefRelations refRels) sliceRels

      -- The parent is a child of another variable, so we relate the child to the grandparent instead
      IsChildOf grandparent relationFromGrandparent -> relateWithLookup (child, childLookup) (relationToChild <> relationFromGrandparent) (grandparent, lookupInternal grandparent refRels sliceRels) refRels sliceRels

--------------------------------------------------------------------------------

-- | Calculates the relation between two variables, O(lg n)
relationBetween :: (GaloisField n, Integral n) => Ref -> Ref -> RefRelations n -> SliceRelations -> Maybe (n, n)
relationBetween var1 var2 refRels sliceRels =
  fromLinRel <$> case (lookupInternal var1 refRels sliceRels, lookupInternal var2 refRels sliceRels) of
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

-- | Convert the relations to specialized constraints
toConstraints :: (GaloisField n, Integral n) => (Ref -> Bool) -> RefRelations n -> Seq (Constraint n)
toConstraints shouldBeKept = Seq.fromList . toList . Map.mapMaybeWithKey convert . unRefRelations
  where
    convert :: (GaloisField n, Integral n) => Ref -> VarStatus n -> Maybe (Constraint n)
    convert var status
      | shouldBeKept var = case status of
          IsConstant val -> Just (CRefFVal var val)
          IsRoot _ -> Nothing
          IsChildOf parent (LinRel slope intercept) ->
            if shouldBeKept parent
              then case (slope, intercept) of
                (0, _) -> Just (CRefFVal var intercept)
                (1, 0) -> Just (CRefEq var parent)
                (_, _) -> case PolyL.fromRefs intercept [(var, -1), (parent, slope)] of
                  Left _ -> error "[ panic ] extractRefRelations: failed to build polynomial"
                  Right poly -> Just (CAddL poly)
              else Nothing
      | otherwise = Nothing

-- | Returns the number of variables in the Reference, O(1)
size :: RefRelations n -> Int
size = Map.size . unRefRelations

-- | A Reference is valid if:
--          1. all children of a parent recognize the parent as their parent
isValid :: (GaloisField n, Integral n) => RefRelations n -> SliceRelations -> Bool
isValid refRels sliceRels = allChildrenRecognizeTheirParent refRels sliceRels && rootsAreSenior refRels

-- | A Reference is valid if all children of a parent recognize the parent as their parent
allChildrenRecognizeTheirParent :: (GaloisField n, Integral n) => RefRelations n -> SliceRelations -> Bool
allChildrenRecognizeTheirParent refRels sliceRels =
  let families = Map.mapMaybe isParent (unRefRelations refRels)

      isParent (IsRoot children) = Just children
      isParent _ = Nothing

      recognizeParent parent child relation = case lookupInternal child refRels sliceRels of
        IsChildOf parent' relation' -> parent == parent' && relation == relation'
        _ -> False
      childrenAllRecognizeParent parent = and . Map.elems . Map.mapWithKey (recognizeParent parent)
   in Map.foldlWithKey' (\acc parent children -> acc && childrenAllRecognizeParent parent children) True families

-- | A Reference is valid if the seniority of the root of a family is greater than equal the seniority of all its children
rootsAreSenior :: RefRelations n -> Bool
rootsAreSenior = Map.foldlWithKey' go True . unRefRelations
  where
    go :: Bool -> Ref -> VarStatus n -> Bool
    go False _ _ = False
    go True _ (IsConstant _) = True
    go True var (IsRoot children) = all (\child -> compareSeniority var child /= LT) (Map.keys children)
    go True var (IsChildOf parent _) = compareSeniority parent var /= LT

--------------------------------------------------------------------------------

data VarStatus n
  = IsConstant n
  | -- | contains the relations to the children
    IsRoot (Map Ref (LinRel n))
  | -- | child = relation parent
    IsChildOf Ref (LinRel n)
  deriving (Show, Eq, Generic, Functor)

instance (NFData n) => NFData (VarStatus n)

-- | Returns the result of looking up a variable, O(lg n)
lookupInternal :: Ref -> RefRelations n -> SliceRelations -> VarStatus n
lookupInternal var (RefRelations refRels) _sliceRels = case Map.lookup var refRels of
  Nothing -> IsRoot mempty
  Just result -> result

--------------------------------------------------------------------------------

-- | Result of looking up a variable in the Relations
data Lookup n = Root | Constant n | ChildOf n Ref n
  deriving (Eq, Show)

lookup :: (GaloisField n) => SliceRelations -> Ref -> RefRelations n -> Lookup n
lookup sliceRels (B (RefUBit refU index)) refRels =
  let -- look in the SliceRelations first
      lookupSliceRelations = case SliceRelations.refUSegmentsRefUBit refU index sliceRels of
        Nothing -> lookupRefRelations
        Just (Left (parent, index')) -> ChildOf 1 (B (RefUBit parent index')) 0
        Just (Right bitVal) -> Constant (if bitVal then 1 else 0)
      -- look in the RefRelations later if we cannot find any result in the SliceRelations
      lookupRefRelations = case lookupInternal (B (RefUBit refU index)) refRels sliceRels of
        IsConstant value -> Constant value
        IsRoot _ -> Root
        IsChildOf parent (LinRel a b) -> ChildOf a parent b
   in lookupSliceRelations
lookup sliceRels var refRels =
  case lookupInternal var refRels sliceRels of
    IsConstant value -> Constant value
    IsRoot _ -> Root
    IsChildOf parent (LinRel a b) -> ChildOf a parent b

-- composeLookup :: (GaloisField n, Integral n) => RefRelations n -> Ref -> Ref -> n -> n -> Lookup n -> Lookup n -> RelM n (RefRelations n)
-- composeLookup xs refA refB slope intercept relationA relationB = case (relationA, relationB) of
--   (Root, Root) ->
--     -- rootA = slope * rootB + intercept
--     relateF refA slope refB intercept xs
--   (Root, Constant n) ->
--     -- rootA = slope * n + intercept
--     assign refA (slope * n + intercept) xs
--   (Root, ChildOf slopeB rootB interceptB) ->
--     -- rootA = slope * refB + intercept && refB = slopeB * rootB + interceptB
--     -- =>
--     -- rootA = slope * (slopeB * rootB + interceptB) + intercept
--     -- =>
--     -- rootA = slope * slopeB * rootB + slope * interceptB + intercept
--     relateF refA (slope * slopeB) rootB (slope * interceptB + intercept) xs
--   (Constant n, Root) ->
--     -- n = slope * rootB + intercept
--     -- =>
--     -- rootB = (n - intercept) / slope
--     assign refB ((n - intercept) / slope) xs
--   (Constant n, Constant m) ->
--     -- n = slope * m + intercept
--     -- =>
--     -- n - intercept = slope * m
--     -- =>
--     -- m = (n - intercept) / slope
--     if m == (n - intercept) / slope
--       then return xs
--       else throwError $ ConflictingValuesF m ((n - intercept) / slope)
--   (Constant n, ChildOf slopeB rootB interceptB) ->
--     -- n = slope * (slopeB * rootB + interceptB) + intercept
--     -- =>
--     -- slope * (slopeB * rootB + interceptB) = n - intercept
--     -- =>
--     -- slopeB * rootB + interceptB = (n - intercept) / slope
--     -- =>
--     -- slopeB * rootB = (n - intercept) / slope - interceptB
--     -- =>
--     -- rootB = ((n - intercept) / slope - interceptB) / slopeB
--     assign rootB (((n - intercept) / slope - interceptB) / slopeB) xs
--   (ChildOf slopeA rootA interceptA, Root) ->
--     -- refA = slopeA * rootA + interceptA = slope * rootB + intercept
--     -- =>
--     -- rootA = (slope * rootB + intercept - interceptA) / slopeA
--     relateF rootA (slope / slopeA) refB ((intercept - interceptA) / slopeA) xs
--   (ChildOf slopeA rootA interceptA, Constant n) ->
--     -- refA = slopeA * rootA + interceptA = slope * n + intercept
--     -- =>
--     -- rootA = (slope * n + intercept - interceptA) / slopeA
--     assign rootA ((slope * n + intercept - interceptA) / slopeA) xs
--   (ChildOf slopeA rootA interceptA, ChildOf slopeB rootB interceptB) ->
--     -- refA = slopeA * rootA + interceptA = slope * (slopeB * rootB + interceptB) + intercept
--     -- =>
--     -- slopeA * rootA = slope * slopeB * rootB + slope * interceptB + intercept - interceptA
--     -- =>
--     -- rootA = (slope * slopeB * rootB + slope * interceptB + intercept - interceptA) / slopeA
--     relateF rootA (slope * slopeB / slopeA) rootB ((slope * interceptB + intercept - interceptA) / slopeA) xs
--   where
--     relateF :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> RefRelations n -> RelM n (RefRelations n)
--     relateF var1 slope' var2 intercept' = relate var1 (LinRel slope' intercept') var2

--------------------------------------------------------------------------------

-- | Relation representing a linear function between two variables, i.e. x = ay + b
data LinRel n = LinRel n n
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

-- | Extracts the coefficients from a LinRel
fromLinRel :: LinRel n -> (n, n)
fromLinRel (LinRel a b) = (a, b)

-- | Render LinRel to some child as a string
renderLinRel :: (GaloisField n, Integral n) => (String, LinRel n) -> String
renderLinRel (var, LinRel x y) = go (LinRel (recip x) (-y / x))
  where
    go (LinRel (-1) 1) = "¬" <> var
    go (LinRel a b) =
      let slope = case a of
            1 -> var
            (-1) -> "-" <> var
            _ -> show (N a) <> var
          intercept = case b of
            0 -> ""
            _ -> " + " <> show (N b)
       in slope <> intercept

-- | Computes the inverse of a relation
--      x = ay + b
--        =>
--      y = (x - b) / a
invertLinRel :: (GaloisField n, Integral n) => LinRel n -> LinRel n
invertLinRel (LinRel a b) = LinRel (recip a) (-b / a)

-- | `execLinRel relation parent = child`
execLinRel :: (GaloisField n, Integral n) => LinRel n -> n -> n
execLinRel (LinRel a b) value = a * value + b

{-# LANGUAGE MultiParamTypeClasses #-}
{-# HLINT ignore "Use list comprehension" #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Data.UnionFind.Boolean2
  ( -- -- * Construction
    -- UnionFind.Map Var Bool,
    -- new,

    -- -- * Operations
    -- assign,
    -- relate,

    -- -- * Lookup
    -- Lookup (..),
    -- lookup,
    -- export,
    REL,

    -- * Testing
    VarStatus (..),
    Error (..),
    isValid,
    validate,
  )
where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Keelung (Var)
import Keelung.Data.Dict (Dict)
import Keelung.Data.Dict qualified as Dict
import Keelung.Data.UnionFind (UnionFind)
import Keelung.Data.UnionFind qualified as UnionFind
import Keelung.Data.UnionFind.Type
import Prelude hiding (lookup)

--------------------------------------------------------------------------------

type REL = UnionFind.Rel Bool

instance UnionFind Var Bool where
  data Map Var Bool = BoolIntMap (IntMap VarStatus) -- relation of each variable
    deriving (Eq)

  -- Relation representing a linear function between two variables, i.e. x = ay + b
  newtype Rel Bool = Rel Bool deriving (Show, Eq)

  new = new
  assign = assign
  relate = relate
  lookup = lookup
  export = export

--------------------------------------------------------------------------------

-- | A variable can be a constant, a root, or a child of another variable.
data VarStatus
  = IsConstant Bool
  | IsRoot
      IntSet -- children with the same sign
      IntSet -- children with the opposite sign
  | IsChildOf
      Var -- root
      Bool -- the same sign as the root
  deriving (Show, Eq)

-- | Create an empty UnionFind.Map Var Bool data structure.
new :: UnionFind.Map Var Bool
new = BoolIntMap mempty

--------------------------------------------------------------------------------

-- data Lookup = Constant Bool | Root | ChildOf Var Bool
--   deriving (Show, Eq)

-- | Status lookup
lookup :: Var -> UnionFind.Map Var Bool -> Lookup Var Bool (UnionFind.Rel Bool)
lookup var (BoolIntMap xs) = case IntMap.lookup var xs of
  Nothing -> Root
  Just (IsConstant b) -> Constant b
  Just (IsRoot _ _) -> Root
  Just (IsChildOf root sign) -> ChildOf root (Rel sign)

-- case lookupInternal var relations of
--   IsConstant value -> Constant value
--   IsRoot _ -> Root
--   IsChildOf parent relation -> ChildOf parent relation

-- -- | Export the UnionFind.Map Var Bool data structure to assignements and relations.
-- export :: UnionFind.Map Var Bool -> (Dict Var Bool, [(IntSet, IntSet)])
-- export (BoolIntMap xs) = (Dict.mapMaybe f xs, map (\(k, (ys, zs)) -> (IntSet.insert k ys, zs)) (IntMap.toList (IntMap.mapMaybe g xs)))
--   where
--     f (IsConstant b) = Just b
--     f _ = Nothing
--     g (IsRoot same opposite) = Just (same, opposite)
--     g _ = Nothing

-- | Exports the UnionFind as a pair of:
--    1. a map from the constant variables to their values
--    2. a map from the root variables to their children with the relation `(slope, intercept)`
export ::
  UnionFind.Map Var Bool ->
  ( Dict Var Bool, -- constants
    Dict Var (Dict Var (UnionFind.Rel Bool)) -- families
  )
export (BoolIntMap relations) = (Dict.fromList constants, Dict.fromList roots)
  where
    constants = IntMap.toList $ IntMap.mapMaybe toConstant relations
    roots = IntMap.toList $ IntMap.mapMaybe toRoot relations

    toConstant (IsConstant value) = Just value
    toConstant _ = Nothing

    toRoot (IsRoot same opposite) = Just $ Dict.fromList $ map (,Rel True) (IntSet.toList same) <> map (,Rel False) (IntSet.toList opposite)
    toRoot _ = Nothing

-- | Assign a value to a variable.
assign :: Var -> Bool -> UnionFind.Map Var Bool -> Maybe (UnionFind.Map Var Bool)
assign var value (BoolIntMap xs) = assign' (BoolIntMap xs) var value (IntMap.lookup var xs)

assign' :: UnionFind.Map Var Bool -> Var -> Bool -> Maybe VarStatus -> Maybe (UnionFind.Map Var Bool)
assign' (BoolIntMap xs) var value varStatus = case varStatus of
  Nothing -> Just $ BoolIntMap $ IntMap.insert var (IsConstant value) xs
  Just (IsConstant v) -> if value == v then Nothing else error "[ panic ] Solver: already assigned with different value"
  Just (IsRoot same opposite) ->
    let withoutChildren = IntMap.withoutKeys (IntMap.withoutKeys xs same) opposite
        rootAssignedValue = IntMap.insert var (IsConstant value) withoutChildren
        childrenOfTheSameSign = IntMap.fromSet (const (IsConstant value)) same
        childrenOfTheOppositeSign = IntMap.fromSet (const (IsConstant (not value))) opposite
     in Just $ BoolIntMap $ rootAssignedValue <> childrenOfTheSameSign <> childrenOfTheOppositeSign
  Just (IsChildOf root sign) -> assign root (sign == value) (BoolIntMap xs)

-- | Relate two variables.
relate :: Var -> Var -> UnionFind.Rel Bool -> UnionFind.Map Var Bool -> Maybe (UnionFind.Map Var Bool)
relate var1 var2 (Rel sign) (BoolIntMap xs) =
  case var1 `compare` var2 of
    LT -> compose (BoolIntMap xs) (var1, IntMap.lookup var1 xs) (var2, IntMap.lookup var2 xs) sign
    EQ -> Nothing
    GT -> compose (BoolIntMap xs) (var2, IntMap.lookup var2 xs) (var1, IntMap.lookup var1 xs) sign

compose :: UnionFind.Map Var Bool -> (Var, Maybe VarStatus) -> (Var, Maybe VarStatus) -> Bool -> Maybe (UnionFind.Map Var Bool)
compose (BoolIntMap xs) (root, status1) (child, status2) sign =
  if root == child
    then Nothing
    else case (status1, status2) of
      (Just (IsConstant value1), _) -> assign' (BoolIntMap xs) child (sign == value1) status2
      (_, Just (IsConstant value2)) -> assign' (BoolIntMap xs) root (sign == value2) status1
      (Nothing, Nothing) ->
        Just $
          BoolIntMap $
            IntMap.insert root (if sign then IsRoot (IntSet.singleton child) mempty else IsRoot mempty (IntSet.singleton child)) $
              IntMap.insert child (IsChildOf root sign) xs
      (Nothing, Just (IsRoot same opposite)) ->
        let grandchildrenSame = IntMap.fromDistinctAscList $ map (,IsChildOf root sign) $ IntSet.toAscList same
            grandchildrenOpposite = IntMap.fromDistinctAscList $ map (,IsChildOf root (not sign)) $ IntSet.toAscList opposite
         in Just $
              BoolIntMap $
                grandchildrenSame
                  <> grandchildrenOpposite
                  <> IntMap.insert root (if sign then IsRoot (IntSet.insert child same) opposite else IsRoot opposite (IntSet.insert child same)) (IntMap.insert child (IsChildOf root sign) xs)
      (Nothing, Just (IsChildOf anotherRoot sign')) ->
        case root `compare` anotherRoot of
          LT -> compose (BoolIntMap xs) (root, Nothing) (anotherRoot, IntMap.lookup anotherRoot xs) (sign == sign')
          EQ -> error "[ panic ] Solver: compose"
          GT -> compose (BoolIntMap xs) (anotherRoot, IntMap.lookup anotherRoot xs) (root, Nothing) (sign == sign')
      (Just (IsRoot same opposite), Nothing) ->
        Just $
          BoolIntMap $
            IntMap.insert root (if sign then IsRoot (IntSet.insert child same) opposite else IsRoot same (IntSet.insert child opposite)) $
              IntMap.insert child (IsChildOf root sign) xs
      (Just (IsChildOf anotherRoot sign'), Nothing) -> relate anotherRoot child (Rel (sign == sign')) (BoolIntMap xs)
      (Just (IsRoot same1 opposite1), Just (IsRoot same2 opposite2)) ->
        let childrenOfChildRemoved = IntMap.withoutKeys (IntMap.withoutKeys xs opposite2) same2
            childrenOfChildUpdated = IntMap.fromSet (const (IsChildOf root sign)) same2 <> IntMap.fromSet (const (IsChildOf root (not sign))) opposite2 <> childrenOfChildRemoved
         in Just
              $ BoolIntMap
              $ IntMap.insert
                root
                ( if sign
                    then IsRoot (IntSet.insert child (same1 <> same2)) (opposite1 <> opposite2)
                    else IsRoot (same1 <> opposite2) (IntSet.insert child (opposite1 <> same2))
                )
              $ IntMap.insert child (IsChildOf root sign) childrenOfChildUpdated
      (Just (IsRoot same1 opposite1), Just (IsChildOf anotherRoot2 sign2)) ->
        case child `compare` anotherRoot2 of
          LT -> compose (BoolIntMap xs) (root, Just (IsRoot same1 opposite1)) (anotherRoot2, IntMap.lookup anotherRoot2 xs) (sign == sign2)
          EQ -> Nothing
          GT -> compose (BoolIntMap xs) (anotherRoot2, IntMap.lookup anotherRoot2 xs) (root, Just (IsRoot same1 opposite1)) (sign == sign2)
      (Just (IsChildOf anotherRoot1 sign1), Just (IsRoot same2 opposite2)) ->
        case child `compare` anotherRoot1 of
          LT -> compose (BoolIntMap xs) (child, Just (IsRoot same2 opposite2)) (anotherRoot1, IntMap.lookup anotherRoot1 xs) (sign == sign1)
          EQ -> Nothing
          GT -> compose (BoolIntMap xs) (anotherRoot1, IntMap.lookup anotherRoot1 xs) (child, Just (IsRoot same2 opposite2)) (sign == sign1)
      (Just (IsChildOf anotherRoot1 sign1), Just (IsChildOf anotherRoot2 sign2)) ->
        if anotherRoot1 < anotherRoot2
          then compose (BoolIntMap xs) (anotherRoot1, IntMap.lookup anotherRoot1 xs) (anotherRoot2, IntMap.lookup anotherRoot2 xs) ((sign1 == sign2) == sign)
          else compose (BoolIntMap xs) (anotherRoot2, IntMap.lookup anotherRoot2 xs) (anotherRoot1, IntMap.lookup anotherRoot1 xs) ((sign1 == sign2) == sign)

--------------------------------------------------------------------------------

data Error
  = InconsistentRelation
      Var -- root
      (UnionFind.Lookup Var Bool (UnionFind.Rel Bool)) -- of root
      Var -- child
      (UnionFind.Lookup Var Bool (UnionFind.Rel Bool)) -- of child
  | MissingRoot
      Var -- child
  | MissingChild
      Var -- root
      Var -- child
  | IsNotRoot
      Var -- root
  | ChildrenMixedTogether
      Var -- root
      IntSet -- children
  | RootAsItsOwnChild
      Var -- root
  deriving (Eq)

instance Show Error where
  show (InconsistentRelation root rootLookup child childLookup) = "Inconsistent relation: root $" <> show root <> " = " <> show rootLookup <> " and child $" <> show child <> " = " <> show childLookup
  show (MissingRoot child) = "Missing root: root of child $" <> show child <> " does not exist"
  show (MissingChild root child) = "Missing child: child $" <> show child <> " of root " <> show root <> " does not exist"
  show (IsNotRoot root) = "Not a root: $" <> show root <> " is not a root"
  show (ChildrenMixedTogether root children) = "Children mixed together: root $" <> show root <> " has children with both signs: " <> show children
  show (RootAsItsOwnChild root) = "Root as its own child: root $" <> show root <> " is its own child"

isValid :: UnionFind.Map Var Bool -> Bool
isValid = null . validate

validate :: UnionFind.Map Var Bool -> [Error]
validate (BoolIntMap xs) = go xs
  where
    go xs' =
      let (xs'', errors) = destructBoolIntMap xs'
       in if xs' == xs'' then errors else go xs''

-- | Try to remove a variable from the data structure
destructBoolIntMap :: IntMap VarStatus -> (IntMap VarStatus, [Error])
destructBoolIntMap xs = case IntMap.maxViewWithKey xs of
  Nothing -> (mempty, [])
  Just ((var, status), xs') -> case status of
    IsConstant _ -> (xs', [])
    IsRoot same opposite ->
      let validateChild expectedSign (child, childStatus) = case childStatus of
            IsConstant value -> [InconsistentRelation var Root child (Constant value)]
            IsRoot _ _ -> [InconsistentRelation var Root child Root]
            IsChildOf root sign -> if root == var && sign == expectedSign then [] else [InconsistentRelation var Root child (ChildOf root (Rel sign))]
          errorsFromChildrenOfTheSameSign = IntMap.toList (IntMap.restrictKeys xs same) >>= validateChild True
          errorsFromChildrenOfTheOppositeSign = IntMap.toList (IntMap.restrictKeys xs opposite) >>= validateChild False
       in if IntSet.null (same `IntSet.intersection` opposite)
            then
              if var `IntSet.member` (same <> opposite)
                then (xs', [RootAsItsOwnChild var])
                else (IntMap.withoutKeys xs' (same <> opposite), errorsFromChildrenOfTheSameSign <> errorsFromChildrenOfTheOppositeSign)
            else (xs', [ChildrenMixedTogether var (same `IntSet.intersection` opposite)])
    IsChildOf root sign -> case IntMap.lookup root xs' of
      Nothing -> (xs', [MissingRoot var])
      Just (IsConstant value) -> (xs', [InconsistentRelation root Root var (Constant value)])
      Just (IsRoot same opposite) ->
        if sign
          then
            if IntSet.member var same
              then (IntMap.insert root (IsRoot (IntSet.delete var same) opposite) xs', [])
              else (xs', [MissingChild root var])
          else
            if IntSet.member var opposite
              then (IntMap.insert root (IsRoot same (IntSet.delete var opposite)) xs', [])
              else (xs', [MissingChild root var])
      Just (IsChildOf _ _) -> (xs', [IsNotRoot root])
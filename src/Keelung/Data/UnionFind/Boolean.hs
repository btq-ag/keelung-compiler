{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use list comprehension" #-}
module Keelung.Data.UnionFind.Boolean
  ( UnionFind,
    empty,

    -- * Operations
    assign,
    relate,

    -- * Lookup
    Lookup (..),
    lookup,
    export,

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
import Debug.Trace
import Keelung (Var)
import Prelude hiding (lookup)

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

newtype UnionFind = UnionFind (IntMap VarStatus) deriving (Show, Eq)

-- | Create an empty UnionFind data structure.
empty :: UnionFind
empty = UnionFind mempty

--------------------------------------------------------------------------------

data Lookup = Constant Bool | Root | ChildOf Var Bool
  deriving (Show, Eq)

-- | Status lookup
lookup :: UnionFind -> Var -> Maybe Lookup
lookup (UnionFind xs) var = case IntMap.lookup var xs of
  Nothing -> Nothing
  Just (IsConstant b) -> Just (Constant b)
  Just (IsRoot _ _) -> Just Root
  Just (IsChildOf root sign) -> Just (ChildOf root sign)

-- | Export the UnionFind data structure to assignements and relations.
export :: UnionFind -> (IntMap Bool, IntMap (IntSet, IntSet))
export (UnionFind xs) = (IntMap.mapMaybe f xs, IntMap.mapMaybe g xs)
  where
    f (IsConstant b) = Just b
    f _ = Nothing
    g (IsRoot same opposite) = Just (same, opposite)
    g _ = Nothing

-- | Assign a value to a variable.
assign :: UnionFind -> Var -> Bool -> UnionFind
assign (UnionFind xs) var value = traceShow xs $ trace ("$" <> show var <> " := " <> show value) $ assign' (UnionFind xs) var value (IntMap.lookup var xs)

assign' :: UnionFind -> Var -> Bool -> Maybe VarStatus -> UnionFind
assign' (UnionFind xs) var value varStatus = case varStatus of
  Nothing -> UnionFind $ IntMap.insert var (IsConstant value) xs
  Just (IsConstant v) -> if value == v then UnionFind xs else error "[ panic ] Solver: already assigned with different value"
  Just (IsRoot same opposite) ->
    let withoutChildren = IntMap.withoutKeys (IntMap.withoutKeys xs same) opposite
        rootAssignedValue = IntMap.insert var (IsConstant value) withoutChildren
        childrenOfTheSameSign = IntMap.fromSet (const (IsConstant value)) same
        childrenOfTheOppositeSign = IntMap.fromSet (const (IsConstant (not value))) opposite
     in UnionFind $ rootAssignedValue <> childrenOfTheSameSign <> childrenOfTheOppositeSign
  Just (IsChildOf root sign) -> assign (UnionFind xs) root (sign == value)

-- | Relate two variables.
relate :: UnionFind -> Var -> Var -> Bool -> UnionFind
relate (UnionFind xs) var1 var2 sign =
  case var1 `compare` var2 of
    LT -> traceShow xs $ trace ("$" <> show var1 <> " == " <> (if sign then "" else "-") <> "$" <> show var2) $ compose (UnionFind xs) (var1, IntMap.lookup var1 xs) (var2, IntMap.lookup var2 xs) sign
    EQ -> UnionFind xs
    GT -> traceShow xs $ trace ("$" <> show var2 <> " == " <> (if sign then "" else "-") <> "$" <> show var1) $ compose (UnionFind xs) (var2, IntMap.lookup var2 xs) (var1, IntMap.lookup var1 xs) sign

compose :: UnionFind -> (Var, Maybe VarStatus) -> (Var, Maybe VarStatus) -> Bool -> UnionFind
compose (UnionFind xs) (root, status1) (child, status2) sign =
  if root == child
    then UnionFind xs
    else case (status1, status2) of
      (Just (IsConstant value1), _) -> assign' (UnionFind xs) child (sign == value1) status2
      (_, Just (IsConstant value2)) -> assign' (UnionFind xs) root (sign == value2) status1
      (Nothing, Nothing) ->
        UnionFind $
          IntMap.insert root (if sign then IsRoot (IntSet.singleton child) mempty else IsRoot mempty (IntSet.singleton child)) $
            IntMap.insert child (IsChildOf root sign) xs
      (Nothing, Just (IsRoot same opposite)) ->
        UnionFind $
          IntMap.insert root (if sign then IsRoot (IntSet.insert child same) opposite else IsRoot opposite (IntSet.insert child same)) $
            IntMap.insert child (IsChildOf root sign) xs
      (Nothing, Just (IsChildOf anotherRoot sign')) ->
        case root `compare` anotherRoot of
          LT -> compose (UnionFind xs) (root, Nothing) (anotherRoot, IntMap.lookup anotherRoot xs) (sign == sign')
          EQ -> error "[ panic ] Solver: compose"
          GT -> compose (UnionFind xs) (anotherRoot, IntMap.lookup anotherRoot xs) (root, Nothing) (sign == sign')
      (Just (IsRoot same opposite), Nothing) ->
        UnionFind $
          IntMap.insert root (if sign then IsRoot (IntSet.insert child same) opposite else IsRoot same (IntSet.insert child opposite)) $
            IntMap.insert child (IsChildOf root sign) xs
      (Just (IsChildOf anotherRoot sign'), Nothing) -> relate (UnionFind xs) anotherRoot child (sign == sign')
      (Just (IsRoot same1 opposite1), Just (IsRoot same2 opposite2)) ->
          let childrenOfChildRemoved = IntMap.withoutKeys (IntMap.withoutKeys xs opposite2) same2
              childrenOfChildUpdated = IntMap.fromSet (const (IsChildOf root sign)) same2 <> IntMap.fromSet (const (IsChildOf root (not sign))) opposite2 <> childrenOfChildRemoved
           in UnionFind
                $ IntMap.insert
                  root
                  ( if sign
                      then IsRoot (IntSet.insert child (same1 <> same2)) (opposite1 <> opposite2)
                      else IsRoot (same1 <> opposite2) (IntSet.insert child (opposite1 <> same2))
                  )
                $ IntMap.insert child (IsChildOf root sign) childrenOfChildUpdated
      (Just (IsRoot same1 opposite1), Just (IsChildOf anotherRoot2 sign2)) ->
        case root `compare` anotherRoot2 of
          LT -> compose (UnionFind xs) (root, Just (IsRoot same1 opposite1)) (anotherRoot2, IntMap.lookup anotherRoot2 xs) (sign == sign2)
          EQ -> UnionFind xs
          GT -> compose (UnionFind xs) (anotherRoot2, IntMap.lookup anotherRoot2 xs) (root, Just (IsRoot same1 opposite1)) (sign == sign2)
      (Just (IsChildOf anotherRoot1 sign1), Just (IsRoot same2 opposite2)) ->
        case root `compare` anotherRoot1 of
          LT -> compose (UnionFind xs) (root, Just (IsRoot same2 opposite2)) (anotherRoot1, IntMap.lookup anotherRoot1 xs) (sign == sign1)
          EQ -> UnionFind xs
          GT -> compose (UnionFind xs) (anotherRoot1, IntMap.lookup anotherRoot1 xs) (root, Just (IsRoot same2 opposite2)) (sign == sign1)
      (Just (IsChildOf anotherRoot1 sign1), Just (IsChildOf anotherRoot2 sign2)) ->
        if anotherRoot1 < anotherRoot2
          then compose (UnionFind xs) (anotherRoot1, IntMap.lookup anotherRoot1 xs) (anotherRoot2, IntMap.lookup anotherRoot2 xs) (sign1 == sign2)
          else compose (UnionFind xs) (anotherRoot2, IntMap.lookup anotherRoot2 xs) (anotherRoot1, IntMap.lookup anotherRoot1 xs) (sign1 == sign2)

--------------------------------------------------------------------------------

data Error
  = InconsistentRelation
      Var -- root
      Lookup -- of root
      Var -- child
      Lookup -- of child
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

isValid :: UnionFind -> Bool
isValid = null . validate

validate :: UnionFind -> [Error]
validate (UnionFind xs) = go xs
  where
    go xs' =
      let (xs'', errors) = destructUnionFind xs'
       in if xs' == xs'' then errors else go xs''

-- | Try to remove a variable from the UnionFind data structure
destructUnionFind :: IntMap VarStatus -> (IntMap VarStatus, [Error])
destructUnionFind xs = case IntMap.maxViewWithKey xs of
  Nothing -> (mempty, [])
  Just ((var, status), xs') -> case status of
    IsConstant _ -> (xs', [])
    IsRoot same opposite ->
      let validateChild expectedSign (child, childStatus) = case childStatus of
            IsConstant value -> [InconsistentRelation var Root child (Constant value)]
            IsRoot _ _ -> [InconsistentRelation var Root child Root]
            IsChildOf root sign -> if root == var && sign == expectedSign then [] else [InconsistentRelation var Root child (ChildOf root sign)]
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
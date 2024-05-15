module Keelung.Data.UnionFind.Boolean (lookup, assign, relate) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
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

newtype UnionFind = UnionFind (IntMap VarStatus)

data Lookup = Constant Bool | Root | ChildOf Var Bool

-- | Status lookup
lookup :: UnionFind -> Var -> Lookup
lookup (UnionFind xs) var = case IntMap.lookup var xs of
  Nothing -> error "[ panic ] Solver: not in UnionFind"
  Just (IsConstant b) -> Constant b
  Just (IsRoot _ _) -> Root
  Just (IsChildOf root sign) -> ChildOf root sign

-- | Assign a value to a variable.
assign :: UnionFind -> Var -> Bool -> UnionFind
assign (UnionFind xs) var value = assign' (UnionFind xs) var value (IntMap.lookup var xs)

assign' :: UnionFind -> Var -> Bool -> Maybe VarStatus -> UnionFind
assign' (UnionFind xs) var value varStatus = case varStatus of
  Nothing -> UnionFind $ IntMap.insert var (IsConstant value) xs
  Just (IsConstant v) -> if value == v then UnionFind xs else error "[ panic ] Solver: already assigned with different value"
  Just (IsRoot same opposite) ->
    let others = IntMap.withoutKeys (IntMap.withoutKeys xs same) opposite
     in UnionFind $ others <> IntMap.fromSet (const (IsConstant value)) same <> IntMap.fromSet (const (IsConstant (not value))) opposite
  Just (IsChildOf root sign) -> assign (UnionFind xs) root (sign == value)

-- | Relate two variables.
relate :: UnionFind -> Var -> Var -> Bool -> UnionFind
relate (UnionFind xs) var1 var2 sign =
  if var1 < var2
    then compose (UnionFind xs) (var1, IntMap.lookup var1 xs) (var2, IntMap.lookup var2 xs) sign
    else compose (UnionFind xs) (var2, IntMap.lookup var2 xs) (var1, IntMap.lookup var1 xs) sign

compose :: UnionFind -> (Var, Maybe VarStatus) -> (Var, Maybe VarStatus) -> Bool -> UnionFind
compose (UnionFind xs) (root, status1) (child, status2) sign = case (status1, status2) of
  (Just (IsConstant value1), _) -> assign' (UnionFind xs) child (sign == value1) status2
  (_, Just (IsConstant value2)) -> assign' (UnionFind xs) root (sign == value2) status1
  (Nothing, Nothing) ->
    UnionFind $
      IntMap.insert root (if sign then IsRoot (IntSet.singleton child) mempty else IsRoot mempty (IntSet.singleton child)) $
        IntMap.insert child (IsChildOf root sign) xs
  (Nothing, Just (IsRoot same opposite)) ->
    UnionFind $
      IntMap.insert root (if sign then IsRoot (IntSet.insert child same) opposite else IsRoot same (IntSet.insert child opposite)) $
        IntMap.insert child (IsChildOf root sign) xs
  (Nothing, Just (IsChildOf anotherRoot sign')) ->
    if root < anotherRoot
      then compose (UnionFind xs) (root, Nothing) (anotherRoot, IntMap.lookup anotherRoot xs) (sign == sign')
      else compose (UnionFind xs) (anotherRoot, IntMap.lookup anotherRoot xs) (root, Nothing) (sign == sign')
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
    if root < anotherRoot2
      then compose (UnionFind xs) (root, Just (IsRoot same1 opposite1)) (anotherRoot2, IntMap.lookup anotherRoot2 xs) (sign == sign2)
      else compose (UnionFind xs) (anotherRoot2, IntMap.lookup anotherRoot2 xs) (root, Just (IsRoot same1 opposite1)) (sign == sign2)
  (Just (IsChildOf anotherRoot1 sign1), Just (IsRoot same2 opposite2)) ->
    if root < anotherRoot1
      then compose (UnionFind xs) (root, Just (IsRoot same2 opposite2)) (anotherRoot1, IntMap.lookup anotherRoot1 xs) (sign == sign1)
      else compose (UnionFind xs) (anotherRoot1, IntMap.lookup anotherRoot1 xs) (root, Just (IsRoot same2 opposite2)) (sign == sign1)
  (Just (IsChildOf anotherRoot1 sign1), Just (IsChildOf anotherRoot2 sign2)) ->
    if anotherRoot1 < anotherRoot2
      then compose (UnionFind xs) (anotherRoot1, IntMap.lookup anotherRoot1 xs) (anotherRoot2, IntMap.lookup anotherRoot2 xs) (sign1 == sign2)
      else compose (UnionFind xs) (anotherRoot2, IntMap.lookup anotherRoot2 xs) (anotherRoot1, IntMap.lookup anotherRoot1 xs) (sign1 == sign2)
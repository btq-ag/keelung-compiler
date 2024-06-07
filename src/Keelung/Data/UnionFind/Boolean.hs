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
import Keelung (Var)
import Keelung.Compiler.Relations.Monad (Seniority (..))
import Keelung.Data.UnionFind.Relation (Relation (..))
import Keelung.Data.UnionFind.Type
import Prelude hiding (lookup)

--------------------------------------------------------------------------------

-- | Export the UnionFind data structure to assignements and relations.
export :: UnionFind Bool Bool -> (IntMap Bool, [(IntSet, IntSet)])
export (UnionFind xs) = (IntMap.mapMaybe f xs, map (\(k, (ys, zs)) -> (IntSet.insert k ys, zs)) (IntMap.toList (IntMap.mapMaybe g xs)))
  where
    f (IsConstant b) = Just b
    f _ = Nothing
    g (IsRoot children) = Just (IntMap.keysSet (IntMap.filter id children), IntMap.keysSet (IntMap.filter not children))
    g _ = Nothing

-- | Assign a value to a variable.
assign :: UnionFind Bool Bool -> Var -> Bool -> UnionFind Bool Bool
assign (UnionFind xs) var value = assign' (UnionFind xs) var value (IntMap.lookup var xs)

assign' :: UnionFind Bool Bool -> Var -> Bool -> Maybe (Status Bool Bool) -> UnionFind Bool Bool
assign' (UnionFind xs) var value varStatus = case varStatus of
  Nothing -> UnionFind $ IntMap.insert var (IsConstant value) xs
  Just (IsConstant v) -> if value == v then UnionFind xs else error "[ panic ] Solver: already assigned with different value"
  Just (IsRoot children) ->
    let withoutChildren = xs `IntMap.difference` children
        rootAssignedValue = IntMap.insert var (IsConstant value) withoutChildren
        childrenValue = fmap (\rel -> if rel then IsConstant value else IsConstant (not value)) children
     in UnionFind $ rootAssignedValue <> childrenValue
  Just (IsChildOf root sign) -> assign (UnionFind xs) root (sign == value)

-- | Relate two variables.
relate :: UnionFind Bool Bool -> Var -> Var -> Bool -> UnionFind Bool Bool
relate (UnionFind xs) var1 var2 sign =
  case var1 `compareSeniority` var2 of
    GT -> compose (UnionFind xs) (var1, IntMap.lookup var1 xs) (var2, IntMap.lookup var2 xs) sign
    EQ -> UnionFind xs
    LT -> compose (UnionFind xs) (var2, IntMap.lookup var2 xs) (var1, IntMap.lookup var1 xs) sign

compose :: UnionFind Bool Bool -> (Var, Maybe (Status Bool Bool)) -> (Var, Maybe (Status Bool Bool)) -> Bool -> UnionFind Bool Bool
compose (UnionFind xs) (root, status1) (child, status2) sign =
  if root == child
    then UnionFind xs
    else case (status1, status2) of
      (Just (IsConstant value1), _) -> assign' (UnionFind xs) child (sign == value1) status2
      (_, Just (IsConstant value2)) -> assign' (UnionFind xs) root (sign == value2) status1
      (Nothing, Nothing) ->
        UnionFind $
          IntMap.insert root (if sign then IsRoot (IntMap.singleton child True) else IsRoot (IntMap.singleton child False)) $
            IntMap.insert child (IsChildOf root sign) xs
      (Nothing, Just (IsRoot children)) ->
        let grandchildren = fmap (\childSign -> IsChildOf root (sign == childSign)) children
         in UnionFind $
              grandchildren
                <> IntMap.insert root (if sign then IsRoot (IntMap.insert child True children) else IsRoot (IntMap.insert child False (fmap not children))) (IntMap.insert child (IsChildOf root sign) xs)
      (Nothing, Just (IsChildOf anotherRoot sign')) ->
        case root `compareSeniority` anotherRoot of
          GT -> compose (UnionFind xs) (root, Nothing) (anotherRoot, IntMap.lookup anotherRoot xs) (sign == sign')
          EQ -> error "[ panic ] Solver: compose"
          LT -> compose (UnionFind xs) (anotherRoot, IntMap.lookup anotherRoot xs) (root, Nothing) (sign == sign')
      (Just (IsRoot children), Nothing) ->
        UnionFind $
          IntMap.insert root (if sign then IsRoot (IntMap.insert child True children) else IsRoot (IntMap.insert child False children)) $
            IntMap.insert child (IsChildOf root sign) xs
      (Just (IsChildOf anotherRoot sign'), Nothing) -> relate (UnionFind xs) anotherRoot child (sign == sign')
      (Just (IsRoot children1), Just (IsRoot children2)) ->
        let childrenOfChildRemoved = xs `IntMap.difference` children2
            childrenOfChildUpdated = fmap (\rel -> if rel then IsChildOf root sign else IsChildOf root (not sign)) children2 <> childrenOfChildRemoved
         in UnionFind
              $ IntMap.insert
                root
                ( if sign
                    then IsRoot (IntMap.insert child True (children1 <> children2))
                    else IsRoot (IntMap.insert child False (children1 <> fmap not children2))
                )
              $ IntMap.insert child (IsChildOf root sign) childrenOfChildUpdated
      (Just (IsRoot children1), Just (IsChildOf anotherRoot2 sign2)) ->
        case root `compareSeniority` anotherRoot2 of
          GT -> compose (UnionFind xs) (root, Just (IsRoot children1)) (anotherRoot2, IntMap.lookup anotherRoot2 xs) (sign == sign2)
          EQ -> UnionFind xs
          LT -> compose (UnionFind xs) (anotherRoot2, IntMap.lookup anotherRoot2 xs) (root, Just (IsRoot children1)) (sign == sign2)
      (Just (IsChildOf anotherRoot1 sign1), Just (IsRoot children2)) ->
        case child `compareSeniority` anotherRoot1 of
          GT -> compose (UnionFind xs) (child, Just (IsRoot children2)) (anotherRoot1, IntMap.lookup anotherRoot1 xs) (sign == sign1)
          EQ -> UnionFind xs
          LT -> compose (UnionFind xs) (anotherRoot1, IntMap.lookup anotherRoot1 xs) (child, Just (IsRoot children2)) (sign == sign1)
      (Just (IsChildOf anotherRoot1 sign1), Just (IsChildOf anotherRoot2 sign2)) ->
        if anotherRoot1 `compareSeniority` anotherRoot2 /= LT
          then compose (UnionFind xs) (anotherRoot1, IntMap.lookup anotherRoot1 xs) (anotherRoot2, IntMap.lookup anotherRoot2 xs) ((sign1 == sign2) == sign)
          else compose (UnionFind xs) (anotherRoot2, IntMap.lookup anotherRoot2 xs) (anotherRoot1, IntMap.lookup anotherRoot1 xs) ((sign1 == sign2) == sign)

--------------------------------------------------------------------------------

instance Relation Bool Bool where
  invert = not
  execute = (==) -- XOR on Bool
  renderWithVar child False = "¬$" <> show child
  renderWithVar child True = "$" <> show child
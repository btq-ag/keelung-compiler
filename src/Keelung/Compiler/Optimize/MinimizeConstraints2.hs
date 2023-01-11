-- This module removes intermediate variables
-- like "X" in the following example:
--
--    A + B = X
--                =>  A + B = C + D
--    C + D = X
--

module Keelung.Compiler.Optimize.MinimizeConstraints2 (run) where

import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set
import Keelung.Compiler.Relocated
import qualified Keelung.Constraint.Polynomial as Poly

--------------------------------------------------------------------------------

run ::
  GaloisField n => 
  IntSet ->
  Set (Constraint n) ->
  Set (Constraint n)
run pinnedVars constraints =
  poolConstraints $
    execState (forM_ constraints dumpInsert) (Pool pinnedVars mempty)

--------------------------------------------------------------------------------

type M n = State (Pool n)

data Pool n = Pool
  { poolPinnedVars :: IntSet,
    poolConstraints :: Set (Constraint n)
  }

-- | Iterate over all constraints and try to merge them with the given constraint.
--   Stops on the first successful merge.
dumpInsert :: GaloisField n => Constraint n -> M n ()
dumpInsert constraint = do
  constraints <- gets poolConstraints
  go (Set.toList constraints)
  where
    go [] = modify' $ \pool -> pool {poolConstraints = Set.insert constraint (poolConstraints pool)}
    go (c : cs) = do
      result <- merge c constraint
      case result of
        -- merge failed, keep going
        Nothing -> go cs
        -- merge success, delete the old constraint and add the new one
        Just new -> do
          modify' $ \pool -> pool {poolConstraints = Set.delete c $ Set.insert new (poolConstraints pool)}
          return () -- abort the loop

-- Returns `Just newConstraint` if the merge is successful.
merge :: GaloisField n => Constraint n -> Constraint n -> M n (Maybe (Constraint n))
merge (CAdd aX) (CAdd bX) = do
  pinned <- gets poolPinnedVars
  return $ case mergePoly pinned aX bX of
    Just bX' -> Just (CAdd bX')
    Nothing -> Nothing
merge (CAdd aX) (CMul dX eX (Left f)) = do
  pinned <- gets poolPinnedVars
  return $ case mergePoly pinned aX dX of
    Just dX' -> Just (CMul dX' eX (Left f))
    Nothing -> do
      case mergePoly pinned aX eX of
        Just eX' -> Just (CMul dX eX' (Left f))
        Nothing -> Nothing
merge (CAdd aX) (CMul dX eX (Right fX)) = do
  pinned <- gets poolPinnedVars
  return $ case mergePoly pinned aX dX of
    Just dX' -> Just (CMul dX' eX (Right fX))
    Nothing -> do
      case mergePoly pinned aX eX of
        Just eX' -> Just (CMul dX eX' (Right fX))
        Nothing -> do
          case mergePoly pinned aX fX of
            Just fX' -> Just (CMul dX eX (Right fX'))
            Nothing -> Nothing
merge a@CMul {} b@CAdd {} = merge b a
merge _ _ = return Nothing

mergePoly :: GaloisField n => IntSet -> Poly.Poly n -> Poly.Poly n -> Maybe (Poly.Poly n)
mergePoly pinned xs ys = do
  let vars = Poly.vars xs `IntSet.intersection` Poly.vars ys `IntSet.difference` pinned
  (var, _) <- IntSet.maxView vars
  -- single out `var` and move it to one side of the equation
  xs' <- Poly.negate <$> Poly.delete var xs
  -- substitute `var` with `xs'`
  Poly.substWithPoly ys var xs'

--------------------------------------------------------------------------------
--
-- In order to bind 2 constraints like:
--
--        A + B = X
--        C * D = X
--
--          into
--
--      A + B = C * D
--
-- We need to find variables like "X" in the above example.
--
-- However, we can't merge 2 constraints like:
--
--        A * B = Y
--        Y * D = E
--
-- Because that would break the degree invariance of `CMul`.
--
-- Variables in `CMul` can only be substituted with polynoimals of degree 1
-- While variables in `CAdd` can be substituted with polynoimals of degree 1 or 2
--
-- data Lock
--   = LockDeg1 Var
--   | LockDeg1or2 Var

-- data Key
--   = KeyDeg1 Var
--   | KeyDeg2 Var

-- -- data BindingSite
-- --   = Degree1 Var
-- --   | Degree1Or2 Var
-- --   deriving (Show)

-- findLocks :: Constraint n -> [Lock]
-- findLocks (CAdd aX) = map LockDeg1or2 $ IntSet.toList $ Poly.vars aX
-- findLocks (CMul aX bX (Left _)) = map LockDeg1 (IntSet.toList (Poly.vars aX <> Poly.vars bX))
-- findLocks (CMul aX bX (Right cX)) = map LockDeg1 (IntSet.toList (Poly.vars aX <> Poly.vars bX <> Poly.vars cX))
-- findLocks (CNEq _ _) = []

-- findKeys :: Constraint n -> [Key]
-- findKeys (CAdd aX) = map KeyDeg1 $ IntSet.toList $ Poly.vars aX
-- findKeys (CMul _ _ (Left _)) = []
-- findKeys (CMul _ _ (Right cX)) = map KeyDeg2 (IntSet.toList $ Poly.vars cX)
-- findKeys (CNEq _ _) = []

-- -- -- | Given a constraint, find all binding sites.
-- -- findBindingSites :: Constraint n -> [BindingSite]
-- -- findBindingSites (CAdd xs) = map Degree1Or2 $ IntSet.toList $ Poly.vars xs
-- -- findBindingSites (CMul aX bX (Left _)) = map Degree1 (IntSet.toList (Poly.vars aX <> Poly.vars bX))
-- -- findBindingSites (CMul aX bX (Right cX)) =
-- --   map Degree1 (IntSet.toList (Poly.vars aX <> Poly.vars bX))
-- --     <> map Degree1Or2 (IntSet.toList $ Poly.vars cX)
-- -- findBindingSites (CNEq _ _) = []

-- --------------------------------------------------------------------------------

-- -- -- Index constraints for later use
-- -- indexConstraints :: Set (Constraint n) -> IntMap (Constraint n)
-- -- indexConstraints = IntMap.fromDistinctAscList . zip [0 .. ] . Set.toList

-- --------------------------------------------------------------------------------

-- --------------------------------------------------------------------------------

-- -- keep track of how many constraints a variable occurs in
-- -- type VarOccurenceMap = IntMap Int

-- -- makeVarOccurenceMap :: Set (Constraint n) -> VarOccurenceMap
-- -- makeVarOccurenceMap = foldr addVarOccurenceMap mempty
-- --   where
-- --     addVarOccurenceMap :: Constraint n -> VarOccurenceMap -> VarOccurenceMap
-- --     addVarOccurenceMap constraint xs =
-- --       let vars = IntSet.toList $ varsInConstraint constraint
-- --        in foldr (IntMap.alter bumpCount) xs vars
-- --       where
-- --         bumpCount :: Maybe Int -> Maybe Int
-- --         bumpCount Nothing = Just 1
-- --         bumpCount (Just n) = Just (n + 1)

-- --------------------------------------------------------------------------------

-- type ConstaintIndex = Int

-- data Soup n = Soup
--   { -- | Constraints in the soup
--     soupConstraints :: IntMap (Constraint n), -- Map ConstaintIndex (Constaint n)
--     -- | "Locks" of degree 1 or 2 in the soup
--     soupLocks1Or2 :: IntMap ConstaintIndex, -- Map Var ConstaintIndex
--     -- | "Locks" of degree 1 in the soup
--     soupLocks1Only :: IntMap ConstaintIndex -- Map Var ConstaintIndex
--   }

-- reactive1 :: Soup n -> Var -> Bool
-- reactive1 soup var =

-- insert :: Soup n -> Constraint n -> Soup n
-- insert soup (CAdd aX) = Poly.vars aX
-- insert soup (CMul po po' e) = _wh
-- insert soup (CNEq n i) = _wi
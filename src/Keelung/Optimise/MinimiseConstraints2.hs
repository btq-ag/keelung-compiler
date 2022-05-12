-- This module removes intermediate variables
-- like "X" in the following example:
--
--    A + B = X
--                =>  A + B = C + D
--    C + D = X
--
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Keelung.Optimise.MinimiseConstraints2 (run) where

-- import Data.IntMap (IntMap)
-- import qualified Data.IntMap as IntMap
-- import Data.IntSet (IntSet)
-- import qualified Data.IntSet as IntSet

-- import Debug.Trace

-- import qualified Keelung.Constraint.Polynomial as Poly

import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import Keelung.Constraint
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Syntax.Common
import qualified Data.Set as Set

--------------------------------------------------------------------------------

run ::
  (GaloisField n, Bounded n, Integral n) =>
  IntSet ->
  Set (Constraint n) ->
  Set (Constraint n)
run pinnedVars constraints = poolConstraints $
  flip execState (Pool pinnedVars mempty) $ do
    forM_ constraints $ \constraint -> insert constraint

-- Pool pinnedVars constraints

--------------------------------------------------------------------------------

-- type M = Reader IntSet -- pinned vars of a constraint system

type M n = State (Pool n)

--
data Pool n = Pool
  { poolPinnedVars :: IntSet,
    poolConstraints :: Set (Constraint n)
  }

insert :: Ord n => Constraint n -> M n ()
insert constraint = do 
  modify' $ \pool -> pool {poolConstraints = Set.insert constraint (poolConstraints pool)}

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
-- findLocks (CMul2 aX bX (Left _)) = map LockDeg1 (IntSet.toList (Poly.vars aX <> Poly.vars bX))
-- findLocks (CMul2 aX bX (Right cX)) = map LockDeg1 (IntSet.toList (Poly.vars aX <> Poly.vars bX <> Poly.vars cX))
-- findLocks (CNQZ _ _) = []

-- findKeys :: Constraint n -> [Key]
-- findKeys (CAdd aX) = map KeyDeg1 $ IntSet.toList $ Poly.vars aX
-- findKeys (CMul2 _ _ (Left _)) = []
-- findKeys (CMul2 _ _ (Right cX)) = map KeyDeg2 (IntSet.toList $ Poly.vars cX)
-- findKeys (CNQZ _ _) = []

-- -- -- | Given a constraint, find all binding sites.
-- -- findBindingSites :: Constraint n -> [BindingSite]
-- -- findBindingSites (CAdd xs) = map Degree1Or2 $ IntSet.toList $ Poly.vars xs
-- -- findBindingSites (CMul2 aX bX (Left _)) = map Degree1 (IntSet.toList (Poly.vars aX <> Poly.vars bX))
-- -- findBindingSites (CMul2 aX bX (Right cX)) =
-- --   map Degree1 (IntSet.toList (Poly.vars aX <> Poly.vars bX))
-- --     <> map Degree1Or2 (IntSet.toList $ Poly.vars cX)
-- -- findBindingSites (CNQZ _ _) = []

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
-- insert soup (CMul2 po po' e) = _wh
-- insert soup (CNQZ n i) = _wi
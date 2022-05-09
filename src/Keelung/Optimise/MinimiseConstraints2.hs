module Keelung.Optimise.MinimiseConstraints2 (run) where

import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import Keelung.Constraint
import Keelung.Syntax.Common
import qualified Data.IntSet as IntSet
import Debug.Trace
-- import qualified Data.Set as Set

--------------------------------------------------------------------------------

run ::
  (GaloisField n, Bounded n, Integral n) =>
  [Var] ->
  Set (Constraint n) ->
  Set (Constraint n)
run _pinnedVars constraints = traceShow (makeVarOccurenceMap constraints) constraints

--   minimised <- minimiseManyTimes constraints
--   return (Set.fromList pinned <> minimised)

--------------------------------------------------------------------------------

-- -- Index constraints for later use 
-- indexConstraints :: Set (Constraint n) -> IntMap (Constraint n)
-- indexConstraints = IntMap.fromDistinctAscList . zip [0 .. ] . Set.toList 

-- -- Find "Bridges" in between constraints
-- -- findBridges :: [Var] -> IntMap (Constraint n) -> [Bridge]
-- -- findBridges candidates constraints = 



-- -- A "Bridge" is a variable that "connects" two or more constraints
-- data Bridge n = Bridge Var [Int] -- indices of constraints



-- findEndpoints :: Constraint n -> [Var]
-- findEndpoints (CAdd n cm) = _wa
-- findEndpoints (CMul x1 x2 x3) = _wb
-- findEndpoints (CNQZ n i) = mempty -- TODO: revise this later



--------------------------------------------------------------------------------

-- keep track of how many constraints a variable occurs in
type VarOccurenceMap = IntMap Int

makeVarOccurenceMap :: Set (Constraint n) -> VarOccurenceMap
makeVarOccurenceMap = foldr addVarOccurenceMap mempty
  where
    addVarOccurenceMap :: Constraint n -> VarOccurenceMap -> VarOccurenceMap
    addVarOccurenceMap constraint xs =
      let vars = IntSet.toList $ varsInConstraint constraint
       in foldr (IntMap.alter bumpCount) xs vars
      where
        bumpCount :: Maybe Int -> Maybe Int
        bumpCount Nothing = Just 1
        bumpCount (Just n) = Just (n + 1)

--------------------------------------------------------------------------------

-- This module removes intermediate variables 
-- like "X" in the following example:
-- 
--    A + B = X
--                =>  A + B = C + D
--    C + D = X   
--

module Keelung.Optimise.MinimiseConstraints2 (run) where

import Data.Field.Galois (GaloisField)
-- import Data.IntMap (IntMap)
-- import qualified Data.IntMap as IntMap
-- import Data.IntSet (IntSet)
-- import qualified Data.IntSet as IntSet
import Data.Set (Set)
-- import Debug.Trace
import Keelung.Constraint
-- import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Syntax.Common


--------------------------------------------------------------------------------

run ::
  (GaloisField n, Bounded n, Integral n) =>
  [Var] ->
  Set (Constraint n) ->
  Set (Constraint n)
run _pinnedVars constraints = constraints

--------------------------------------------------------------------------------
-- 
-- In order to bind 2 constraints like:
-- 
--        A + B = X
--        C + D = X    
-- 
--          into    
-- 
--      A + B = C + D
-- 
-- We need to find "binding sites" like variable "X" in the above example.
-- 
-- Since we can rearrange variables in `CAdd` 
-- All variables in `CAdd` are valid binding sites.
-- 
-- However, for variables in `CMul`, for example, in "X * Y = Z"
-- 



--------------------------------------------------------------------------------

-- -- Index constraints for later use
-- indexConstraints :: Set (Constraint n) -> IntMap (Constraint n)
-- indexConstraints = IntMap.fromDistinctAscList . zip [0 .. ] . Set.toList

-- -- Find "Bridges" in between constraints
-- -- findBridges :: [Var] -> IntMap (Constraint n) -> [Bridge]
-- -- findBridges candidates constraints =

-- -- A "Bridge" is a variable that "connects" two or more constraints
-- data Bridge n = Bridge Var [Int] -- indices of constraints

-- -- | An "Endpoint" of a constraint is a Variable in that constraint
-- --   that can be substituted for a polynomial
-- findEndpoints :: Constraint n -> IntSet
-- findEndpoints (CAdd xs) = Poly.vars xs
-- findEndpoints (CMul2 aX bX cX) = IntSet.unions $ filter ((== 1) . IntSet.size) $ map Poly.vars [aX, bX, cX]
-- findEndpoints (CNQZ n i) = mempty -- TODO: revise this later

--------------------------------------------------------------------------------

-- --------------------------------------------------------------------------------

-- -- keep track of how many constraints a variable occurs in
-- type VarOccurenceMap = IntMap Int

-- makeVarOccurenceMap :: Set (Constraint n) -> VarOccurenceMap
-- makeVarOccurenceMap = foldr addVarOccurenceMap mempty
--   where
--     addVarOccurenceMap :: Constraint n -> VarOccurenceMap -> VarOccurenceMap
--     addVarOccurenceMap constraint xs =
--       let vars = IntSet.toList $ varsInConstraint constraint
--        in foldr (IntMap.alter bumpCount) xs vars
--       where
--         bumpCount :: Maybe Int -> Maybe Int
--         bumpCount Nothing = Just 1
--         bumpCount (Just n) = Just (n + 1)

-- --------------------------------------------------------------------------------

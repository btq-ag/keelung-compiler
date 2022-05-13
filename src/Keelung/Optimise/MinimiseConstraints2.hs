-- This module removes intermediate variables
-- like "X" in the following example:
--
--    A + B = X
--                =>  A + B = C + D
--    C + D = X
--

module Keelung.Optimise.MinimiseConstraints2 (run) where


import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set
import Keelung.Constraint
import qualified Keelung.Constraint.Polynomial as Poly

--------------------------------------------------------------------------------

run ::
  (GaloisField n, Bounded n, Integral n) =>
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
dumpInsert :: (Ord n, Num n, Show n, Bounded n, Integral n, Fractional n) => Constraint n -> M n ()
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
merge :: (Ord n, Num n, Eq n, Show n, Bounded n, Integral n, Fractional n) => Constraint n -> Constraint n -> M n (Maybe (Constraint n))
merge (CAdd aX) (CAdd bX) = do
  pinned <- gets poolPinnedVars
  let candidateVars = Poly.vars aX `IntSet.intersection` Poly.vars bX `IntSet.difference` pinned
  -- pick a variable
  case IntSet.maxView candidateVars of
    Nothing -> return Nothing
    Just (var, _) -> do
      let result = do
            -- in Maybe Monad
            aX' <- Poly.negate <$> Poly.delete var aX
            -- substitute `var` with `aX'`
            bX' <- Poly.substitute bX var aX'
            return $ CAdd bX'
      return result
merge (CAdd aX) (CMul2 dX eX (Left f)) = do
  pinned <- gets poolPinnedVars
  -- in `dX`
  let candidateVarsInDX =
        (Poly.vars aX `IntSet.intersection` Poly.vars dX)
          `IntSet.difference` pinned
  case IntSet.maxView candidateVarsInDX of
    Just (var, _) -> do
      let result = do
            -- move and single out `var` to one side of the equation
            aX' <- Poly.negate <$> Poly.delete var aX
            -- substitute `var` with `aX'`
            dX' <- Poly.substitute dX var aX'
            return (CMul2 dX' eX (Left f))
      return result
    Nothing -> do
      let result = do
            let candidateVarsInEX =
                  (Poly.vars aX `IntSet.intersection` Poly.vars eX)
                    `IntSet.difference` pinned
            (var, _) <- IntSet.maxView candidateVarsInEX
            -- move and single out `var` to one side of the equation
            aX' <- Poly.negate <$> Poly.delete var aX
            -- substitute `var` with `aX'`
            eX' <- Poly.substitute eX var aX'
            return (CMul2 dX eX' (Left f))
      return result
merge (CAdd aX) (CMul2 dX eX (Right fX)) = do
  pinned <- gets poolPinnedVars
  -- in `dX`
  let candidateVarsInDX =
        (Poly.vars aX `IntSet.intersection` Poly.vars dX)
          `IntSet.difference` pinned
  case IntSet.maxView candidateVarsInDX of
    Just (var, _) -> do
      let result = do
            -- move and single out `var` to one side of the equation
            aX' <- Poly.negate <$> Poly.delete var aX
            -- substitute `var` with `aX'`
            dX' <- Poly.substitute dX var aX'
            return (CMul2 dX' eX (Right fX))
      return result
    Nothing -> do
      let result = do
            let candidateVarsInEX =
                  (Poly.vars aX `IntSet.intersection` Poly.vars eX)
                    `IntSet.difference` pinned
            case IntSet.maxView candidateVarsInEX of
              Just (var, _) -> do
                -- move and single out `var` to one side of the equation
                aX' <- Poly.negate <$> Poly.delete var aX
                -- substitute `var` with `aX'`
                eX' <- Poly.substitute eX var aX'
                return (CMul2 dX eX' (Right fX))
              Nothing -> do
                let candidateVarsInFX =
                      (Poly.vars aX `IntSet.intersection` Poly.vars fX)
                        `IntSet.difference` pinned
                case IntSet.maxView candidateVarsInFX of
                  Just (var, _) -> do
                    -- move and single out `var` to one side of the equation
                    aX' <- Poly.negate <$> Poly.delete var aX
                    -- substitute `var` with `aX'`
                    fX' <- Poly.substitute fX var aX'
                    return (CMul2 dX eX (Right fX'))
                  Nothing -> Nothing
      return result
merge a@CMul2 {} b@CAdd {} = merge b a
merge _ _ = return Nothing

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
module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

-- import Control.Monad.State

import Control.Monad.State
import Data.Bifunctor (second)
import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Constraint
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG

run :: (GaloisField n, Integral n) => ConstraintSystem n -> ConstraintSystem n
run cs =
  let (csAddF', (changed, cs')) = runAddM cs $ do
        foldM goThroughAddFM [] (csAddF cs)
      cs'' = cs' {csAddF = csAddF'}
   in if changed == NothingChanged
        then cs''
        else run cs''

-- goThroughUnionFindF :: (GaloisField n, Integral n) => UnionFind RefF n -> UnionFind RefF n
-- goThroughUnionFindF unionFind =

goThroughAddFM :: (GaloisField n, Integral n) => [PolyG RefF n] -> PolyG RefF n -> AddM n [PolyG RefF n]
goThroughAddFM acc poly = do
  unionFind <- gets (csVarEqF . snd)
  changed <- classifyAdd poly
  if changed
    then return acc
    else do
      case substPolyG unionFind poly of
        Nothing -> return (poly : acc)
        Just (poly', substitutedRefs) -> do
          markChanged AdditiveConstraintChanged
          updateConstraintSystem $ \cs -> cs {csOccurrenceF = removeOccurrences substitutedRefs $ removeOccurrencesWithPolyG poly' (csOccurrenceF cs)}
          return (poly' : acc)

------------------------------------------------------------------------------

data WhatChanged
  = NothingChanged
  | RelationChanged
  | AdditiveConstraintChanged
  deriving (Eq, Show)

instance Semigroup WhatChanged where
  NothingChanged <> x = x
  x <> NothingChanged = x
  RelationChanged <> _ = RelationChanged
  _ <> RelationChanged = RelationChanged
  AdditiveConstraintChanged <> _ = AdditiveConstraintChanged

-- _ <> AdditiveConstraintChanged = AdditiveConstraintChanged

instance Monoid WhatChanged where
  mempty = NothingChanged

------------------------------------------------------------------------------

type AddM n = State (WhatChanged, ConstraintSystem n)

runAddM :: ConstraintSystem n -> AddM n a -> (a, (WhatChanged, ConstraintSystem n))
runAddM cs m = runState m (NothingChanged, cs)

markChanged :: WhatChanged -> AddM n ()
markChanged whatChanged = modify' $ \(_, cs) -> (whatChanged, cs)

updateConstraintSystem :: (ConstraintSystem n -> ConstraintSystem n) -> AddM n ()
updateConstraintSystem = modify' . second

-- | Go through additive constraints and classify them into relation constraints when possible.
--   Returns 'True' if the constraint has been reduced.
classifyAdd :: (GaloisField n, Integral n) => PolyG RefF n -> AddM n Bool
classifyAdd poly = case PolyG.view poly of
  (_, []) -> error "[ panic ] Empty polynomial"
  (intercept, [(var, slope)]) -> do
    --    intercept + slope * var = 0
    --  =>
    --    var = - intercept / slope
    markChanged RelationChanged

    updateConstraintSystem $ \cs ->
      cs
        { csVarEqF = UnionFind.bindToValue var (-intercept / slope) (csVarEqF cs),
          csOccurrenceF = removeOccurrences [var] (csOccurrenceF cs)
        }
    return True
  (intercept, [(var1, slope1), (var2, slope2)]) -> do
    --    intercept + slope1 * var1 + slope2 * var2 = 0
    --  =>
    --    slope1 * var1 = - slope2 * var2 - intercept
    --  =>
    --    var1 = - slope2 * var2 / slope1 - intercept / slope1
    cs <- gets snd
    case UnionFind.relate var1 (-slope2 / slope1, var2, -intercept / slope1) (csVarEqF cs) of
      Nothing -> return False
      Just unionFind' -> do
        markChanged RelationChanged
        updateConstraintSystem $ \cs' -> cs' {csVarEqF = unionFind', csOccurrenceF = removeOccurrences [var1, var2] (csOccurrenceF cs)}
        return True
  (_, _) -> return False
module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

-- import Control.Monad.State

import Control.Monad.State
import Data.Bifunctor (second)
import Data.Field.Galois (GaloisField)
import Data.Map.Strict qualified as Map
import Keelung.Compiler.Constraint
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG

run :: (GaloisField n, Integral n) => ConstraintSystem n -> ConstraintSystem n
run cs =
  let (csAddF', (changed, cs')) = runAddM cs $ do
        foldM goThroughAddFM [] (csAddF cs)
      cs'' = cs' {csAddF = csAddF'}
   in if changed
        then run cs''
        else cs''

goThroughAddFM :: (GaloisField n, Integral n) => [PolyG RefF n] -> PolyG RefF n -> AddM n [PolyG RefF n]
goThroughAddFM acc poly = do
  unionFind <- gets (csVarEqF . snd)
  changed <- classifyAdd poly
  if changed
    then return acc
    else do
      case substPolyG2 unionFind poly of
        Nothing -> return (poly : acc)
        Just (poly', substitutedRefs) -> do
          setToChanged
          updateConstraintSystem $ \cs -> cs {csOccurrenceF = removeOccurrences substitutedRefs $ removeOccurrencesWithPolyG poly' (csOccurrenceF cs)}
          return (poly' : acc)

------------------------------------------------------------------------------

type AddM n = State (Bool, ConstraintSystem n)

runAddM :: ConstraintSystem n -> AddM n a -> (a, (Bool, ConstraintSystem n))
runAddM cs m = runState m (False, cs)

setToChanged :: AddM n ()
setToChanged = modify' $ \(_, cs) -> (True, cs)

updateConstraintSystem :: (ConstraintSystem n -> ConstraintSystem n) -> AddM n ()
updateConstraintSystem = modify' . second

-- updateUnionFind :: (UnionFind RefF n -> UnionFind RefF n) -> AddM n ()
-- updateUnionFind f = modify' $ \(changed, cs) -> (changed, cs {csVarEqF = f (csVarEqF cs)})

-- | Decide whether to keep the Add constraint or not.
classifyAdd :: (GaloisField n, Integral n) => PolyG RefF n -> AddM n Bool
classifyAdd poly = case PolyG.view poly of
  (_, []) -> error "[ panic ] Empty polynomial"
  (intercept, [(var, slope)]) -> do
    --    intercept + slope * var = 0
    --  =>
    --    var = - intercept / slope
    setToChanged
    updateConstraintSystem $ \cs -> cs {csVarBindF = Map.insert var (-intercept / slope) (csVarBindF cs), csOccurrenceF = removeOccurrences [var] (csOccurrenceF cs)}
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
        setToChanged
        updateConstraintSystem $ \cs' -> cs' {csVarEqF = unionFind', csOccurrenceF = removeOccurrences [var1, var2] (csOccurrenceF cs)}
        return True
  (_, _) -> return False
module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

-- import Control.Monad.State

import Control.Monad.State
import Control.Monad.Writer
import Data.Field.Galois (GaloisField)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Keelung.Compiler.Constraint
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG

run :: (GaloisField n, Integral n) => ConstraintSystem n -> ConstraintSystem n
run cs =
  let ((csAddF', learned), cs') = runAddM cs $ do
        foldM goThroughAddFM [] (csAddF cs)
      cs'' = cs' {csAddF = csAddF', csVarBindF = csVarBindF cs <> learnedFromAddBind learned}
   in if learned /= mempty
        then run cs''
        else cs''

goThroughAddFM :: (GaloisField n, Integral n) => [PolyG RefF n] -> PolyG RefF n -> AddM n [PolyG RefF n]
goThroughAddFM acc poly = do
  unionFind <- gets csVarEqF
  case substPolyG unionFind poly of
    Nothing -> return (poly : acc)
    Just (poly', unionFind', substitutedRefs) -> do
      modify' $ \cs -> cs {csVarEqF = unionFind'}
      keep <- classifyAdd poly'
      if keep
        then return (poly' : acc)
        else do
          modify' $ \cs -> cs {csOccurrenceF = removeOccurrences substitutedRefs $ removeOccurrencesWithPolyG poly' (csOccurrenceF cs)}
          return acc

newtype LearnedFromAdd n = LearnedFromAdd
  { -- learnedFromAddEq :: Seq (RefF, (n, RefF)),
    learnedFromAddBind :: Map RefF n
  }
  deriving (Eq, Show)

instance Semigroup (LearnedFromAdd n) where
  LearnedFromAdd bind1 <> LearnedFromAdd bind2 = LearnedFromAdd (bind1 <> bind2)

instance Monoid (LearnedFromAdd n) where
  mempty = LearnedFromAdd mempty

------------------------------------------------------------------------------

type AddM n = WriterT (LearnedFromAdd n) (State (ConstraintSystem n))

runAddM :: ConstraintSystem n -> AddM n a -> ((a, LearnedFromAdd n), ConstraintSystem n)
runAddM cs m = runState (runWriterT m) cs

-- | Decide whether to keep the Add constraint or not.
classifyAdd :: (GaloisField n, Integral n) => PolyG RefF n -> AddM n Bool
classifyAdd poly = case PolyG.view poly of
  (_, []) -> error "[ panic ] Empty polynomial"
  (intercept, [(var, slope)]) -> do
    tell $ mempty {learnedFromAddBind = Map.singleton var (-intercept / slope)}
    return False
  (intercept, [(var1, slope1), (var2, slope2)]) -> do
    --    intercept + slope1 * var1 + slope2 * var2 = 0
    --  =>
    --    var1 = - intercept / slope1 - slope2 / slope1 * var2
    modify' $ \cs -> cs {csVarEqF = UnionFind.union var1 (-slope2 / slope1, var2, -intercept / slope1) (csVarEqF cs)}
    return False
  (_, _) -> return True

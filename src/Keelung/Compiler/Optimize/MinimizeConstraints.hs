module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

-- import Control.Monad.State

import Control.Monad.State
import Control.Monad.Writer
import Data.Field.Galois (GaloisField)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Keelung.Compiler.Constraint
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind)
import qualified Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind as UnionFind
import Keelung.Data.PolyG (PolyG)
import qualified Keelung.Data.PolyG as PolyG

-- import Control.Monad.State.Strict

-- run :: (GaloisField n, Integral n) => ConstraintSystem n -> ConstraintSystem n
-- run cs =
--   let unionFindF = csVarEqF cs
--       (changed, unionFindF', csAddF') = foldl goThroughAddF (False, unionFindF, []) (csAddF cs)
--    in if changed
--         then cs {csVarEqF = unionFindF', csAddF = csAddF'}
--         else cs

run :: (GaloisField n, Integral n) => ConstraintSystem n -> ConstraintSystem n
run cs =
  let ((csAddF', learned), unionFindF') = runAddM (csVarEqF cs) $ do
        foldM goThroughAddFM [] (csAddF cs)
      cs' = cs {csVarEqF = unionFindF', csAddF = csAddF', csVarBindF = csVarBindF cs <> learnedFromAddBind learned}
   in if learned /= mempty
        then run cs'
        else cs'

goThroughAddFM :: (GaloisField n, Integral n) => [PolyG RefF n] -> PolyG RefF n -> AddM n [PolyG RefF n]
goThroughAddFM acc poly = do
  unionFind <- get
  case substPolyG unionFind poly of
    Nothing -> return (poly : acc)
    Just (poly', unionFind') -> do
      put unionFind'
      keep <- classifyAdd poly'
      if keep
        then return (poly' : acc)
        else return acc

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

type AddM n = WriterT (LearnedFromAdd n) (State (UnionFind RefF n))

runAddM :: UnionFind RefF n -> AddM n a -> ((a, LearnedFromAdd n), UnionFind RefF n)
runAddM unoinFind m = runState (runWriterT m) unoinFind

classifyAdd :: (GaloisField n, Integral n) => PolyG RefF n -> AddM n Bool
classifyAdd poly = case PolyG.view poly of
  (_, []) -> error "[ panic ] Empty polynomial"
  (0, [(var, _)]) -> do
    tell $ mempty {learnedFromAddBind = Map.singleton var 0}
    return False
  (0, [(var1, c), (var2, d)]) -> do
    modify' $ \unionFind -> UnionFind.union var1 (-d / c, var2) unionFind
    return False
  (0, _) -> return True
  (c, [(var, coeff)]) -> do
    tell $ mempty {learnedFromAddBind = Map.singleton var (-c / coeff)}
    return False
  (_, _) -> return True

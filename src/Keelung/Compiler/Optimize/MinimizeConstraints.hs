module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

-- import Control.Monad.State

import Control.Monad.State
import Control.Monad.Writer
import Data.Field.Galois (GaloisField)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Keelung.Compiler.Constraint
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind)
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
  let unionFindF = csVarEqF cs
      ((csAddF', learned), unionFindF') = runAddM unionFindF $ do
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
      tell $ classifyAdd poly'
      return (poly' : acc)

data LearnedFromAdd n = LearnedFromAdd
  { learnedFromAddEq :: Seq (RefF, RefF),
    learnedFromAddBind :: Map RefF n
  }
  deriving (Eq, Show)

instance Semigroup (LearnedFromAdd n) where
  LearnedFromAdd eq1 bind1 <> LearnedFromAdd eq2 bind2 = LearnedFromAdd (eq1 <> eq2) (bind1 <> bind2)

instance Monoid (LearnedFromAdd n) where
  mempty = LearnedFromAdd mempty mempty

------------------------------------------------------------------------------

type AddM n = WriterT (LearnedFromAdd n) (State (UnionFind RefF))

runAddM :: UnionFind RefF -> AddM n a -> ((a, LearnedFromAdd n), UnionFind RefF)
runAddM unoinFind m = runState (runWriterT m) unoinFind

classifyAdd :: (GaloisField n, Integral n) => PolyG RefF n -> LearnedFromAdd n
classifyAdd poly = case PolyG.view poly of
  (_, []) -> error "[ panic ] Empty polynomial"
  (0, [(var, _)]) -> mempty {learnedFromAddBind = Map.singleton var 0}
  (0, [(var1, -1), (var2, 1)]) -> mempty {learnedFromAddEq = Seq.singleton (var1, var2)}
  (0, [(var1, 1), (var2, -1)]) -> mempty {learnedFromAddEq = Seq.singleton (var1, var2)}
  (0, _) -> mempty
  (c, [(var, coeff)]) -> mempty {learnedFromAddBind = Map.singleton var (-c / coeff)}
  (_, _) -> mempty

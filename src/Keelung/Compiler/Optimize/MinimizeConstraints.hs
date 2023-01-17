module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

-- import Control.Monad.State

import Control.Monad.State
import Control.Monad.Writer
import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Constraint
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind)
import Keelung.Data.PolyG (PolyG)

-- import Control.Monad.State.Strict

run :: (GaloisField n, Integral n) => ConstraintSystem n -> ConstraintSystem n
run cs =
  let unionFindF = csVarEqF cs
      (changed, unionFindF', csAddF') = foldl goThroughAddF (False, unionFindF, []) (csAddF cs)
   in if changed
        then cs {csVarEqF = unionFindF', csAddF = csAddF'}
        else cs

-- run2 :: (GaloisField n, Integral n) => ConstraintSystem n -> ConstraintSystem n
-- run2 cs =
--   let unionFindF = csVarEqF cs
--       (changed, unionFindF', csAddF') = runAddM unionFindF $ do 
--         foldM goThroughAddFM [] (csAddF cs)
        
--         -- foldl goThroughAddF (False, unionFindF, []) (csAddF cs)
--    in if changed
--         then cs {csVarEqF = unionFindF', csAddF = csAddF'}
--         else cs

goThroughAddF :: (GaloisField n, Integral n) => (Bool, UnionFind RefF, [PolyG RefF n]) -> PolyG RefF n -> (Bool, UnionFind RefF, [PolyG RefF n])
goThroughAddF (changed, unionFind, acc) poly = case substPolyG unionFind poly of
  Nothing -> (changed, unionFind, poly : acc)
  Just (poly', unionFind') -> (True, unionFind', poly' : acc)

-- goThroughAddFM :: (GaloisField n, Integral n) => [PolyG RefF n] -> PolyG RefF n -> AddM n [PolyG RefF n]
-- goThroughAddFM acc poly = do 
--   unionFind <- get
--   case substPoly unionFind poly of
--     Nothing -> return (poly : acc)
--     Just (poly', unionFind') -> do 
      
--       (True, unionFind', poly' : acc)

data LearnedFromAdd = LearnedEqFromAdd [(RefF, RefF)] | LeanredNothingFromAdd
  deriving (Eq, Show)

instance Semigroup LearnedFromAdd where
  LeanredNothingFromAdd <> x = x
  x <> LeanredNothingFromAdd = x
  LearnedEqFromAdd xs <> LearnedEqFromAdd ys = LearnedEqFromAdd (xs <> ys)

------------------------------------------------------------------------------

type AddM n = WriterT LearnedFromAdd (State (UnionFind RefF))

runAddM :: UnionFind RefF -> AddM n a -> ((a, LearnedFromAdd), UnionFind RefF)
runAddM unoinFind m = runState (runWriterT m) unoinFind

-- classifyAdd :: (GaloisField n, Integral n) => PolyG RefF n -> AddM n LearnedFromAdd
-- classifyAdd poly = case Poly.coeff 
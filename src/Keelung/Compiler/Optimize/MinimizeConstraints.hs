module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

-- import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Constraint
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind)

-- import Control.Monad.State.Strict

run :: (GaloisField n, Integral n) => ConstraintSystem n -> ConstraintSystem n
run cs =
  let unionFindF = csVarEqF cs
      (changed, unionFindF', csAddF') = foldl go (False, unionFindF, []) (csAddF cs)
   in if changed
        then cs {csVarEqF = unionFindF', csAddF = csAddF'}
        else cs

go :: (GaloisField n, Integral n) => (Bool, UnionFind RefF, [Poly' RefF n]) -> Poly' RefF n -> (Bool, UnionFind RefF, [Poly' RefF n])
go (changed, unionFind, acc) poly = case substPoly unionFind poly of
  Nothing -> (changed, unionFind, poly : acc)
  Just (poly', unionFind') -> (True, unionFind', poly' : acc)

------------------------------------------------------------------------------

-- type M n = State (ConstraintSystem n)

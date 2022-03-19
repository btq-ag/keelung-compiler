{-# LANGUAGE DeriveFunctor #-}

module Keelung.Constraint.CoeffMap
  ( CoeffMap,
    fromList,
    toList,
    toIntMap,
    null,
    insert,
    keysSet,
    mapKeys,
  )
where

import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import Data.Semiring (plus, zero)
import Prelude hiding (null)

type Var = Int

-- INVARIANT:
--  1. No key appears more than once.
--  2. Upon duplicate insertion, insert field sum of the values.
--  3. No terms with coefficient of 0.

newtype CoeffMap f = CoeffMap {toIntMap :: IntMap f}
  deriving (Eq, Ord, Functor)

instance (Show f, Eq f, Num f) => Show (CoeffMap f) where
  show = go . IntMap.toList . toIntMap
    where
      go [] = " = 0"
      go [terms] = printTerm terms ++ go []
      go (term : xs) = printTerm term ++ " + " ++ go xs

      printTerm (_, 0) = ""
      printTerm (x, 1) = "$" ++ show x
      printTerm (x, -1) = "-$" ++ show x
      printTerm (x, c) = show c ++ "$" ++ show x

fromList :: GaloisField f => [(Var, f)] -> CoeffMap f
fromList xs = CoeffMap . IntMap.filter (zero /=) $ IntMap.fromListWith plus xs

toList :: CoeffMap f -> [(Var, f)]
toList = IntMap.toList . toIntMap

null :: CoeffMap f -> Bool
null = IntMap.null . toIntMap

insert :: GaloisField f => Var -> f -> CoeffMap f -> CoeffMap f
insert var x = CoeffMap . IntMap.insertWith plus var x . toIntMap

keysSet :: CoeffMap f -> IntSet
keysSet = IntMap.keysSet . toIntMap

mapKeys :: (Var -> Var) -> CoeffMap f -> CoeffMap f
mapKeys f = CoeffMap . IntMap.mapKeys f . toIntMap

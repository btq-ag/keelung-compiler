{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Relations.Reference
  ( RefRelations,
    new,
    assignR,
    relateB,
    relateR,
    relationBetween,
    toConstraints,
    lookup,
    EquivClass.Lookup (..),
  )
where

import Data.Field.Galois (GaloisField)
import Data.Sequence (Seq)
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Relations.Slice (SliceRelations)
import Keelung.Data.Constraint (Constraint)
import Keelung.Data.Reference
import Prelude hiding (lookup)

type RefRelations n = EquivClass.EquivClass n

--------------------------------------------------------------------------------

new :: RefRelations n
new = EquivClass.new "References Relations"

-- | Note: `RefUBit` should not be allowed here
assignR :: (GaloisField n, Integral n) => Ref -> n -> RefRelations n -> EquivClass.M n (RefRelations n)
assignR = EquivClass.assign

relateB :: (GaloisField n, Integral n) => RefB -> (Bool, RefB) -> RefRelations n -> EquivClass.M n (RefRelations n)
relateB = EquivClass.relateB

-- var = slope * var2 + intercept
relateR :: (GaloisField n, Integral n) => SliceRelations -> Ref -> n -> Ref -> n -> RefRelations n -> EquivClass.M n (RefRelations n)
relateR = EquivClass.relateR

relationBetween :: (GaloisField n, Integral n) => Ref -> Ref -> RefRelations n -> Maybe (n, n)
relationBetween = EquivClass.relationBetween

-- | Convert the relations to specialized constraints
toConstraints :: (GaloisField n, Integral n) => (Ref -> Bool) -> RefRelations n -> Seq (Constraint n)
toConstraints = EquivClass.toConstraints

--------------------------------------------------------------------------------

lookup :: (GaloisField n) => SliceRelations -> Ref -> RefRelations n -> EquivClass.Lookup n
lookup = EquivClass.lookup
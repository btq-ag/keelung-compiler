{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Relations
  ( Relations (..),
    new,
    assignR,
    assignB,
    assignS,
    relateB,
    -- relateL,
    relateR,
    relateS,
    relationBetween,
    size,
    lookup,
    Ref.Lookup (..),
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Options (Options)
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Relations.Reference qualified as Ref
import Keelung.Compiler.Relations.Slice qualified as SliceRelations
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U qualified as U
import Prelude hiding (lookup)

data Relations n = Relations
  { relationsR :: Ref.RefRelations n,
    relationsS :: SliceRelations.SliceRelations,
    relationsOptions :: Options
  }
  deriving (Eq, Generic, NFData)

instance (GaloisField n, Integral n) => Show (Relations n) where
  show (Relations refs slices _) =
    (if EquivClass.size refs == 0 then "" else show refs)
      <> (if SliceRelations.size slices == 0 then "" else show slices)

updateRelationsR ::
  (Ref.RefRelations n -> EquivClass.M (Error n) (Ref.RefRelations n)) ->
  Relations n ->
  EquivClass.M (Error n) (Relations n)
updateRelationsR f xs = do
  relations <- f (relationsR xs)
  return $ xs {relationsR = relations}

--------------------------------------------------------------------------------

new :: Options -> Relations n
new = Relations Ref.new SliceRelations.new

assignR :: (GaloisField n, Integral n) => Ref -> n -> Relations n -> EquivClass.M (Error n) (Relations n)
assignR var val relations = case var of
  B (RefUBit refU i) ->
    if val == 0 || val == 1
      then assignS (Slice.Slice refU i (i + 1)) (toInteger val) relations
      else throwError $ InvalidBooleanValue val
  _ -> updateRelationsR (Ref.assignR var val) relations

assignB :: (GaloisField n, Integral n) => RefB -> Bool -> Relations n -> EquivClass.M (Error n) (Relations n)
assignB ref val = assignR (B ref) (if val then 1 else 0)

assignS :: (GaloisField n, Integral n) => Slice -> Integer -> Relations n -> EquivClass.M (Error n) (Relations n)
assignS slice int relations = do
  EquivClass.markChanged
  return $
    relations
      { relationsS = SliceRelations.assign slice (U.new (Slice.sliceEnd slice - Slice.sliceStart slice) int) (relationsS relations)
      }

relateB :: (GaloisField n, Integral n) => (GaloisField n) => RefB -> (Bool, RefB) -> Relations n -> EquivClass.M (Error n) (Relations n)
relateB refA (polarity, refB) = updateRelationsR (Ref.relateB refA (polarity, refB))

-- var = slope * var2 + intercept
relateR :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> Relations n -> EquivClass.M (Error n) (Relations n)
relateR x slope y intercept xs = updateRelationsR (Ref.relateR (relationsS xs) x slope y intercept) xs

relateS :: (GaloisField n, Integral n) => Slice -> Slice -> Relations n -> EquivClass.M (Error n) (Relations n)
relateS slice1 slice2 relations = do
  EquivClass.markChanged
  return $
    relations
      { relationsS = SliceRelations.relate slice1 slice2 (relationsS relations)
      }

relationBetween :: (GaloisField n, Integral n) => Ref -> Ref -> Relations n -> Maybe (n, n)
relationBetween var1 var2 = Ref.relationBetween var1 var2 . relationsR

size :: Relations n -> Int
size (Relations refs slices _) = EquivClass.size refs + SliceRelations.size slices

--------------------------------------------------------------------------------

lookup :: (GaloisField n) => Ref -> Relations n -> Ref.Lookup n
lookup var xs = Ref.lookup (relationsS xs) var (relationsR xs)

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Relations
  ( Relations (..),
    RelM,
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
    RefRelations.Lookup (..),
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Options (Options)
import Keelung.Compiler.Relations.Monad
import Keelung.Compiler.Relations.Reference qualified as RefRelations
import Keelung.Compiler.Relations.Slice qualified as SliceRelations
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U qualified as U
import Prelude hiding (lookup)

data Relations n = Relations
  { relationsR :: RefRelations.RefRelations n,
    relationsS :: SliceRelations.SliceRelations,
    relationsOptions :: Options
  }
  deriving (Eq, Generic, NFData, Functor)

instance (GaloisField n, Integral n) => Show (Relations n) where
  show (Relations refs slices _) =
    (if RefRelations.size refs == 0 then "" else show refs)
      <> (if SliceRelations.size slices == 0 then "" else show slices)

updateRelationsR ::
  (RefRelations.RefRelations n -> RelM n (Maybe (RefRelations.RefRelations n))) ->
  Relations n ->
  RelM n (Maybe (Relations n))
updateRelationsR f xs = do
  result <- f (relationsR xs)
  case result of
    Nothing -> return Nothing
    Just relations -> return $ Just $ xs {relationsR = relations}

--------------------------------------------------------------------------------

new :: Options -> Relations n
new = Relations RefRelations.new SliceRelations.new

assignR :: (GaloisField n, Integral n) => Ref -> n -> Relations n -> RelM n (Maybe (Relations n))
assignR var val relations = case var of
  B (RefUBit refU i) ->
    if val == 0 || val == 1
      then assignS (Slice.Slice refU i (i + 1)) (toInteger val) relations
      else throwError $ InvalidBooleanValue val
  _ -> updateRelationsR (RefRelations.assign var val) relations

assignB :: (GaloisField n, Integral n) => RefB -> Bool -> Relations n -> RelM n (Maybe (Relations n))
assignB ref val = assignR (B ref) (if val then 1 else 0)

assignS :: (GaloisField n, Integral n) => Slice -> Integer -> Relations n -> RelM n (Maybe (Relations n))
assignS slice int relations =
  return $
    Just $
      relations
        { relationsS = SliceRelations.assign slice (U.new (Slice.sliceEnd slice - Slice.sliceStart slice) int) (relationsS relations)
        }

relateB :: (GaloisField n, Integral n) => (GaloisField n) => RefB -> (Bool, RefB) -> Relations n -> RelM n (Maybe (Relations n))
relateB refA (polarity, refB) = updateRelationsR (RefRelations.relateB refA (polarity, refB))

-- var = slope * var2 + intercept
relateR :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> Relations n -> RelM n (Maybe (Relations n))
relateR x slope y intercept = updateRelationsR (RefRelations.relateR x slope y intercept)

relateS :: (GaloisField n, Integral n) => Slice -> Slice -> Relations n -> RelM n (Maybe (Relations n))
relateS slice1 slice2 relations = do
  return $
    Just $
      relations
        { relationsS = SliceRelations.relate slice1 slice2 (relationsS relations)
        }

relationBetween :: (GaloisField n, Integral n) => Ref -> Ref -> Relations n -> Maybe (n, n)
relationBetween var1 var2 = RefRelations.relationBetween var1 var2 . relationsR

size :: Relations n -> Int
size (Relations refs slices _) = RefRelations.size refs + SliceRelations.size slices

--------------------------------------------------------------------------------

lookup :: (GaloisField n) => Ref -> Relations n -> RefRelations.Lookup n
lookup var xs = RefRelations.lookup (relationsS xs) var (relationsR xs)

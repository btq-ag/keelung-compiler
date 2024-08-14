{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Manages the relations between variables and slices.
--
--    * RefRel: bianry relation on 2 Refs
--        * 2 Refs `x` and `y` are related by RefRel if `x = a * y + b` where `a` is not 0.
--        * RefRel is symmetric, reflexive and transitive. This makes it an equivalence relation.
--
--    * SliceRel: binary relation on 2 Slices
--        * 2 Slices `s1` and `s2` are related by SliceRel if `s1 = s2`
--        * SliceRel is symmetric, reflexive and transitive. This makes it an equivalence relation.
module Keelung.Compiler.Relations
  ( -- * Construction
    Relations (..),
    RelM,
    runRelM,
    new,

    -- * Operations
    assignRef,
    assignSlice,
    relateRef,
    relateRefB,
    relateSlice,

    -- * Queries
    relationBetween,
    size,
    lookupRef,
    RefRelations.Lookup (..),

    -- * Testing
    Error (..),
    isValid,
    validate,
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Error qualified as Compiler
import Keelung.Compiler.Options (Options)
import Keelung.Compiler.Relations.Monad
import Keelung.Compiler.Relations.Reference qualified as RefRelations
import Keelung.Compiler.Relations.Slice qualified as SliceRelations
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U qualified as U
import Keelung.Data.UnionFind.Field qualified as Field
import Prelude hiding (lookup)

--------------------------------------------------------------------------------

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

-- | Construct with Options.
new :: Options -> Relations n
new = Relations RefRelations.new SliceRelations.new

-- | Helper function for updating the RefRelations.
updateRefRelations ::
  (RefRelations.RefRelations n -> SliceRelations.SliceRelations -> RelM n (Maybe (RefRelations.RefRelations n))) ->
  Relations n ->
  RelM n (Maybe (Relations n))
updateRefRelations f xs = do
  result <- f (relationsR xs) (relationsS xs)
  case result of
    Nothing -> return Nothing
    Just relations -> return $ Just $ xs {relationsR = relations}

--------------------------------------------------------------------------------

-- | Assign a Ref to a constant value.
assignRef :: (GaloisField n, Integral n) => Ref -> n -> Relations n -> RelM n (Maybe (Relations n))
assignRef var val relations = case var of
  B (RefUBit refU i) ->
    if val == 0 || val == 1
      then assignSlice (Slice.Slice refU i (i + 1)) (toInteger val) relations
      else throwError $ Compiler.InvalidBooleanValue val
  _ -> updateRefRelations (RefRelations.assign var val) relations

-- | Assign a Slice to a constant value.
assignSlice :: (GaloisField n, Integral n) => Slice -> Integer -> Relations n -> RelM n (Maybe (Relations n))
assignSlice slice int relations =
  return $
    Just $
      relations
        { relationsS = SliceRelations.assign slice (U.new (Slice.sliceEnd slice - Slice.sliceStart slice) int) (relationsS relations)
        }

-- | Relate two Refs.
--    var = slope * var2 + intercept
relateRef :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> Relations n -> RelM n (Maybe (Relations n))
relateRef x slope y intercept = updateRefRelations (RefRelations.relate x slope y intercept)

-- | Specialized version of `relateRef` for relating two RefBs.
relateRefB :: (GaloisField n, Integral n) => (GaloisField n) => RefB -> (Bool, RefB) -> Relations n -> RelM n (Maybe (Relations n))
relateRefB refA (polarity, refB) = updateRefRelations (RefRelations.relateB refA (polarity, refB))

-- | Relate two Slices.
relateSlice :: (GaloisField n, Integral n) => Slice -> Slice -> Relations n -> RelM n (Maybe (Relations n))
relateSlice slice1 slice2 relations = do
  return $
    Just $
      relations
        { relationsS = SliceRelations.relate slice1 slice2 (relationsS relations)
        }

relationBetween :: (GaloisField n, Integral n) => Ref -> Ref -> Relations n -> Maybe (Field.LinRel n)
relationBetween var1 var2 relations = uncurry Field.LinRel <$> RefRelations.relationBetween var1 var2 (relationsR relations) (relationsS relations)

size :: Relations n -> Int
size (Relations refs slices _) = RefRelations.size refs + SliceRelations.size slices

--------------------------------------------------------------------------------

lookupRef :: (GaloisField n) => Ref -> Relations n -> RefRelations.Lookup n
lookupRef var xs = RefRelations.lookup (relationsS xs) var (relationsR xs)

--------------------------------------------------------------------------------

data Error = RefError RefRelations.Error | SliceError SliceRelations.Error
  deriving (Show, Eq)

-- | See if the data structure is in a valid state.
isValid :: (GaloisField n, Integral n) => Relations n -> Bool
isValid (Relations refs slices _) = RefRelations.isValid refs slices && SliceRelations.isValid slices

validate :: (GaloisField n, Integral n) => Relations n -> [Error]
validate (Relations refs slices _) = map RefError (RefRelations.validate refs slices) ++ map SliceError (SliceRelations.validate slices)
{-# LANGUAGE FlexibleInstances #-}

-- | Module for testing and reporting variable reindexing
module Keelung.Compiler.Linker.ReindexReport (test, Error (..)) where

import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Map qualified as Map
import Data.Sequence (Seq)
import Data.Set (Set)
import Data.Set qualified as Set
import Keelung (Var)
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.Linker
import Keelung.Data.Constraint (Constraint (..))
import Keelung.Data.Limb (Limb)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)

test :: (Integral n, GaloisField n) => ConstraintModule n -> Maybe Error
test cm = checkReport $ generateReindexReport (constructEnv cm) cm

--------------------------------------------------------------------------------

-- | Datatype for keeping track of which Ref is mapped to which Var
newtype ReindexReport = ReindexReport (IntMap (Set Ref))

-- | How to show a ReindexReport
instance Show ReindexReport where
  show (ReindexReport xs) =
    "Reindexing: \n"
      <> unlines
        ( map
            ( \(var, set) ->
                show var
                  <> " => "
                  <> ( if Set.size set == 1
                         then show (Set.findMin set)
                         else show (Set.toList set)
                     )
            )
            (IntMap.toList xs)
        )

-- | How to combine two reports
instance Semigroup ReindexReport where
  ReindexReport a <> ReindexReport b = ReindexReport (IntMap.unionWith (<>) a b)

-- | The empty report
instance Monoid ReindexReport where
  mempty = ReindexReport IntMap.empty

--------------------------------------------------------------------------------

data Error
  = VarSkipped IntSet -- Vars skipped after reindexing
  | MultipleRefs [(Var, Set Ref)] -- Multiple refs mapped to the same Var
  deriving (Show, Eq)

checkReport :: ReindexReport -> Maybe Error
checkReport (ReindexReport xs) =
  let skippedVars = IntSet.fromDistinctAscList [0 .. IntMap.size xs - 1] IntSet.\\ IntMap.keysSet xs
      multipleRefs = filter (\(_, s) -> Set.size s > 1) (IntMap.toList xs)
   in if IntSet.null skippedVars
        then
          if null multipleRefs
            then Nothing
            else Just (MultipleRefs multipleRefs)
        else Just (VarSkipped skippedVars)

--------------------------------------------------------------------------------

-- | Typeclass for generating ReindexReport
class GenerateReindexReport a where
  generateReindexReport :: Env -> a -> ReindexReport

instance GenerateReindexReport Limb where
  generateReindexReport env limb =
    ReindexReport $
      -- precondition of `fromDistinctAscList` is that the keys are in ascending order
      IntMap.fromDistinctAscList
        [ ( reindexRefU
              env
              (Limb.lmbRef limb)
              (i + Limb.lmbOffset limb),
            Set.singleton (B (RefUBit (Limb.lmbRef limb) i))
          )
          | i <- [0 .. Limb.lmbWidth limb - 1]
        ]

instance GenerateReindexReport Slice where
  generateReindexReport env slice =
    ReindexReport $
      -- precondition of `fromDistinctAscList` is that the keys are in ascending order
      IntMap.fromDistinctAscList
        [ ( reindexRefU
              env
              (Slice.sliceRefU slice)
              i,
            Set.singleton (B (RefUBit (Slice.sliceRefU slice) i))
          )
          | i <- [Slice.sliceStart slice .. Slice.sliceEnd slice - 1]
        ]

instance (GenerateReindexReport a) => GenerateReindexReport (Seq a) where
  generateReindexReport env xs = mconcat $ map (generateReindexReport env) (toList xs)

instance (GenerateReindexReport a) => GenerateReindexReport [a] where
  generateReindexReport env xs = mconcat $ map (generateReindexReport env) xs

instance GenerateReindexReport RefF where
  generateReindexReport env ref = ReindexReport $ IntMap.singleton (reindexRefF env ref) (Set.singleton (F ref))

instance GenerateReindexReport RefB where
  generateReindexReport env ref = ReindexReport $ IntMap.singleton (reindexRefB env ref) (Set.singleton (B ref))

instance GenerateReindexReport Ref where
  generateReindexReport env (F refF) = generateReindexReport env refF
  generateReindexReport env (B refB) = generateReindexReport env refB

instance GenerateReindexReport RefU where
  generateReindexReport env refU = generateReindexReport env (Limb.refUToLimbs (envFieldWidth env) refU)

instance GenerateReindexReport (PolyL n) where
  generateReindexReport env poly =
    let limbReindexReport = generateReindexReport env (fmap fst (PolyL.polyLimbs poly))
        refReindexReport = generateReindexReport env (Map.keys (PolyL.polyRefs poly))
     in limbReindexReport <> refReindexReport

instance GenerateReindexReport (Constraint n) where
  generateReindexReport env (CAddL poly) = generateReindexReport env poly
  generateReindexReport env (CRefEq x y) = generateReindexReport env x <> generateReindexReport env y
  generateReindexReport env (CRefBNEq x y) = generateReindexReport env x <> generateReindexReport env y
  generateReindexReport env (CLimbEq x y) = generateReindexReport env x <> generateReindexReport env y
  generateReindexReport env (CRefUEq x y) = generateReindexReport env x <> generateReindexReport env y
  generateReindexReport env (CSliceEq x y) = generateReindexReport env x <> generateReindexReport env y
  generateReindexReport env (CRefFVal x _) = generateReindexReport env x
  generateReindexReport env (CLimbVal x _) = generateReindexReport env x
  generateReindexReport env (CRefUVal x _) = generateReindexReport env x
  generateReindexReport env (CMulL a b (Left _)) = generateReindexReport env a <> generateReindexReport env b
  generateReindexReport env (CMulL a b (Right c)) = generateReindexReport env a <> generateReindexReport env b <> generateReindexReport env c
  generateReindexReport env (CSliceVal x _) = generateReindexReport env x

instance GenerateReindexReport (Either RefU U) where
  generateReindexReport env (Left refU) = generateReindexReport env refU
  generateReindexReport _ (Right _) = mempty

instance (Integral n, GaloisField n) => GenerateReindexReport (ConstraintModule n) where
  generateReindexReport env cm =
    let fromModInvs (a, b, c, _) = generateReindexReport env a <> generateReindexReport env b <> generateReindexReport env c
        fromCLDivMods (a, b, c, d) = generateReindexReport env a <> generateReindexReport env b <> generateReindexReport env c <> generateReindexReport env d
        fromDivMods (a, b, c, d) = generateReindexReport env a <> generateReindexReport env b <> generateReindexReport env c <> generateReindexReport env d
        fromEqZeros (a, b) = generateReindexReport env a <> generateReindexReport env b
     in mconcat $
          toList $
            fmap (generateReindexReport env) (toConstraints cm env)
              <> fmap fromEqZeros (cmEqZeros cm)
              <> fmap fromDivMods (cmDivMods cm)
              <> fmap fromCLDivMods (cmCLDivMods cm)
              <> fmap fromModInvs (cmModInvs cm)
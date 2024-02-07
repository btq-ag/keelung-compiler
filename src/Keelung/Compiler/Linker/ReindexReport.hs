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
import Keelung.Compiler.Util (showList')
import Keelung.Data.Constraint (Constraint (..))
import Keelung.Data.Limb (Limb)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Syntax.Counters (Counters)
import Keelung.Syntax.Counters qualified as Counters

test :: (Integral n, GaloisField n) => ConstraintModule n -> Maybe Error
test cm = checkReport (envNewCounters (constructEnv cm)) $ generateReindexReport (constructEnv cm) [] cm

--------------------------------------------------------------------------------

-- | Ref with a String tag
data TaggedRef = TaggedRef Ref [String]

instance Show TaggedRef where
  show (TaggedRef ref []) = show ref
  show (TaggedRef ref tags) = show ref <> " " <> showList' tags

instance Eq TaggedRef where
  TaggedRef ref1 _ == TaggedRef ref2 _ = ref1 == ref2

instance Ord TaggedRef where
  TaggedRef ref1 _ `compare` TaggedRef ref2 _ = ref1 `compare` ref2

-- | Datatype for keeping track of which Ref is mapped to which Var
newtype ReindexReport = ReindexReport (IntMap (Set TaggedRef))

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
  | MultipleRefs [(Var, Set TaggedRef)] -- Multiple refs mapped to the same Var
  deriving (Show, Eq)

-- | See if the report is valid, else return an error:
--      1. Check if any vars correspond to multiple refs
--      2. Check if any vars are skipped (except for pinned vars like public inputs, private inputs, and outputs)
checkReport :: Counters -> ReindexReport -> Maybe Error
checkReport counters (ReindexReport xs) =
  let skippedVars = IntSet.fromDistinctAscList [0 .. IntMap.size xs - 1] IntSet.\\ IntMap.keysSet xs
      pinnedVarCount = Counters.getCount counters Counters.Output + Counters.getCount counters Counters.PublicInput + Counters.getCount counters Counters.PrivateInput
      skippedVarsExcludingPinnedVars = IntSet.filter (>= pinnedVarCount) skippedVars
      multipleRefs = filter (\(_, s) -> Set.size s > 1) (IntMap.toList xs)
   in if null multipleRefs
        then
          if IntSet.null skippedVarsExcludingPinnedVars
            then Nothing
            else Just (VarSkipped skippedVars)
        else Just (MultipleRefs multipleRefs)

--------------------------------------------------------------------------------

-- | Typeclass for generating ReindexReport
class GenerateReindexReport a where
  generateReindexReport :: Env -> [String] -> a -> ReindexReport

instance GenerateReindexReport Limb where
  generateReindexReport env tags limb =
    ReindexReport $
      IntMap.fromList
        [ ( reindexRefU
              env
              (Limb.lmbRef limb)
              (i + Limb.lmbOffset limb),
            Set.singleton (TaggedRef (B (RefUBit (Limb.lmbRef limb) (i + Limb.lmbOffset limb))) tags)
          )
          | i <- [0 .. Limb.lmbWidth limb - 1]
        ]

instance GenerateReindexReport Slice where
  generateReindexReport env tags slice =
    ReindexReport $
      IntMap.fromList
        [ ( reindexRefU
              env
              (Slice.sliceRefU slice)
              i,
            Set.singleton (TaggedRef (B (RefUBit (Slice.sliceRefU slice) i)) tags)
          )
          | i <- [Slice.sliceStart slice .. Slice.sliceEnd slice - 1]
        ]

instance (GenerateReindexReport a) => GenerateReindexReport (Seq a) where
  generateReindexReport env tags xs = mconcat $ map (generateReindexReport env tags) (toList xs)

instance (GenerateReindexReport a) => GenerateReindexReport [a] where
  generateReindexReport env tags xs = mconcat $ map (generateReindexReport env tags) xs

instance GenerateReindexReport RefF where
  generateReindexReport env tags ref = ReindexReport $ IntMap.singleton (reindexRefF env ref) (Set.singleton (TaggedRef (F ref) tags))

instance GenerateReindexReport RefB where
  generateReindexReport env tags ref = ReindexReport $ IntMap.singleton (reindexRefB env ref) (Set.singleton (TaggedRef (B ref) tags))

instance GenerateReindexReport Ref where
  generateReindexReport env tags (F refF) = generateReindexReport env tags refF
  generateReindexReport env tags (B refB) = generateReindexReport env tags refB

instance GenerateReindexReport RefU where
  generateReindexReport env tags refU = generateReindexReport env tags (Limb.refUToLimbs (envFieldWidth env) refU)

instance GenerateReindexReport (PolyL n) where
  generateReindexReport env tags poly =
    let limbReindexReport = generateReindexReport env tags (fmap fst (PolyL.polyLimbs poly))
        refReindexReport = generateReindexReport env tags (Map.keys (PolyL.polyRefs poly))
     in limbReindexReport <> refReindexReport

instance GenerateReindexReport (Constraint n) where
  generateReindexReport env tags (CAddL poly) = generateReindexReport env ("CAddL" : tags) poly
  generateReindexReport env tags (CRefEq x y) = generateReindexReport env ("CRefEq L" : tags) x <> generateReindexReport env ("CRefEq R" : tags) y
  generateReindexReport env tags (CRefBNEq x y) = generateReindexReport env ("CRefBNEq L" : tags) x <> generateReindexReport env ("CRefBNEq R" : tags) y
  generateReindexReport env tags (CLimbEq x y) = generateReindexReport env ("CLimbEq L" : tags) x <> generateReindexReport env ("CLimbEq R" : tags) y
  generateReindexReport env tags (CSliceEq x y) = generateReindexReport env ("CSliceEq L" : tags) x <> generateReindexReport env ("CSliceEq R" : tags) y
  generateReindexReport env tags (CRefFVal x _) = generateReindexReport env ("CRefFVal" : tags) x
  generateReindexReport env tags (CLimbVal x _) = generateReindexReport env ("CLimbVal" : tags) x
  generateReindexReport env tags (CMulL a b (Left _)) = generateReindexReport env ("CMulL a" : tags) a <> generateReindexReport env ("CMulL b" : tags) b
  generateReindexReport env tags (CMulL a b (Right c)) = generateReindexReport env ("CMulL a" : tags) a <> generateReindexReport env ("CMulL b" : tags) b <> generateReindexReport env ("CMulL c" : tags) c
  generateReindexReport env tags (CSliceVal x _) = generateReindexReport env ("CSliceVal" : tags) x

instance GenerateReindexReport (Either RefU U) where
  generateReindexReport env tags (Left refU) = generateReindexReport env tags refU
  generateReindexReport _ _ (Right _) = mempty

instance (Integral n, GaloisField n) => GenerateReindexReport (ConstraintModule n) where
  generateReindexReport env tags cm =
    let fromModInvs (a, b, c, _) = generateReindexReport env ("ModInv a" : tags) a <> generateReindexReport env ("ModInv b" : tags) b <> generateReindexReport env ("ModInv c" : tags) c
        fromCLDivMods (a, b, c, d) = generateReindexReport env ("ClDivMod a" : tags) a <> generateReindexReport env ("ClDivMod b" : tags) b <> generateReindexReport env ("ClDivMod c" : tags) c <> generateReindexReport env ("ClDivMod d" : tags) d
        fromDivMods (a, b, c, d) = generateReindexReport env ("DivMod a" : tags) a <> generateReindexReport env ("DivMod b" : tags) b <> generateReindexReport env ("DivMod c" : tags) c <> generateReindexReport env ("DivMod d" : tags) d
        fromEqZeros (a, b) = generateReindexReport env ("EqZero a" : tags) a <> generateReindexReport env ("EqZero b" : tags) b
     in mconcat $
          toList $
            fmap (generateReindexReport env tags) (toConstraints cm env)
              <> fmap fromEqZeros (cmEqZeros cm)
              <> fmap fromDivMods (cmDivMods cm)
              <> fmap fromCLDivMods (cmCLDivMods cm)
              <> fmap fromModInvs (cmModInvs cm)
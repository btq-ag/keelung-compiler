{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module Keelung.Compiler.ConstraintModule
  ( ConstraintModule (..),
    relocateConstraintModule,
    sizeOfConstraintModule,
    UpdateOccurrences (..),
  )
where

import Control.Arrow (first, left)
import Control.DeepSeq (NFData)
import Data.Bifunctor (bimap)
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung.Compiler.Constraint
import Keelung.Compiler.Optimize.OccurB (OccurB)
import Keelung.Compiler.Optimize.OccurB qualified as OccurB
import Keelung.Compiler.Optimize.OccurF (OccurF)
import Keelung.Compiler.Optimize.OccurF qualified as OccurF
import Keelung.Compiler.Optimize.OccurU (OccurU)
import Keelung.Compiler.Optimize.OccurU qualified as OccurU
import Keelung.Compiler.Relations.Boolean (BooleanRelations)
import Keelung.Compiler.Relations.Boolean qualified as BooleanRelations
import Keelung.Compiler.Relations.Field (AllRelations)
import Keelung.Compiler.Relations.Field qualified as AllRelations
import Keelung.Compiler.Relations.Field qualified as FieldRelations
import Keelung.Compiler.Relations.UInt (UIntRelations)
import Keelung.Compiler.Relations.UInt qualified as UIntRelations
import Keelung.Compiler.Relocated qualified as Relocated
import Keelung.Compiler.Util (indent)
import Keelung.Data.BinRep (BinRep (..))
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Data.Struct
import Keelung.Data.VarGroup (showList', toSubscript)
import Keelung.Field (FieldType)
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

-- | A constraint module is a collection of constraints with some additional information
data ConstraintModule n = ConstraintModule
  { cmField :: (FieldType, Integer, Integer),
    cmCounters :: !Counters,
    -- for counting the occurences of variables in constraints (excluding the ones that are in FieldRelations)
    cmOccurrenceF :: !OccurF,
    cmOccurrenceB :: !OccurB,
    cmOccurrenceU :: !OccurU,
    cmBitTests :: !(IntMap IntSet),
    cmBinReps :: [[(RefB, Int)]],
    -- when x == y (FieldRelations)
    cmFieldRelations :: AllRelations n,
    -- cmUIntRelations :: UIntRelations n,
    -- addative constraints
    cmAddF :: [PolyG Ref n],
    -- multiplicative constraints
    cmMulF :: [(PolyG Ref n, PolyG Ref n, Either n (PolyG Ref n))],
    -- hits for computing equality
    cmEqZeros :: [(PolyG Ref n, RefF)],
    -- hints for generating witnesses for DivMod constraints
    -- a = b * q + r
    cmDivMods :: [(Either RefU n, Either RefU n, Either RefU n, Either RefU n)],
    -- hints for generating witnesses for ModInv constraints
    cmModInvs :: [(Either RefU n, Either RefU n, Integer)]
  }
  deriving (Eq, Generic, NFData)

instance (GaloisField n, Integral n) => Show (ConstraintModule n) where
  show cm =
    "Constraint Module {\n"
      <> showVarEqF
      -- <> showVarEqU
      <> showAddF
      <> showMulF
      <> showEqs
      <> showBooleanConstraints
      <> showDivModHints
      <> showModInvHints
      <> showOccurrencesF
      <> showOccurrencesB
      <> showOccurrencesU
      <> showVariables
      <> "}"
    where
      counters = cmCounters cm
      -- sizes of constraint groups
      booleanConstraintCount = getBooleanConstraintCount counters

      adapt :: String -> [a] -> (a -> String) -> String
      adapt name xs f =
        let size = length xs
         in if size == 0
              then ""
              else "  " <> name <> " (" <> show size <> "):\n\n" <> unlines (map (("    " <>) . f) xs) <> "\n"

      -- Boolean constraints
      showBooleanConstraints =
        if booleanConstraintCount == 0
          then ""
          else
            "  Boolean constriants ("
              <> show booleanConstraintCount
              <> "):\n\n"
              <> unlines (map ("    " <>) (prettyBooleanConstraints counters))
              <> "\n"

      showDivModHints =
        if null $ cmDivMods cm
          then ""
          else "  DivMod hints:\n" <> indent (indent (showList' (map (\(x, y, q, r) -> show x <> " = " <> show y <> " * " <> show q <> " + " <> show r) (cmDivMods cm))))

      showModInvHints =
        if null $ cmModInvs cm
          then ""
          else "  ModInv hints:\n" <> indent (indent (showList' (map (\(x, _n, p) -> show x <> "⁻¹ = (mod " <> show p <> ")") (cmModInvs cm))))

      showVarEqF = "  Field relations:\n" <> indent (indent (show (cmFieldRelations cm)))

      showAddF = adapt "AddF" (cmAddF cm) show

      showMulF = adapt "MulF" (cmMulF cm) showMul

      showEqs = adapt "Eqs" (cmEqZeros cm) $ \(poly, m) ->
        "Eqs " <> show poly <> " / " <> show m

      showOccurrencesF =
        if OccurF.null $ cmOccurrenceF cm
          then ""
          else "  OccruencesF:\n  " <> indent (showList' (map (\(var, n) -> show (RefFX var) <> ": " <> show n) (OccurF.toList $ cmOccurrenceF cm)))
      showOccurrencesB =
        if OccurB.null $ cmOccurrenceB cm
          then ""
          else "  OccruencesB:\n  " <> indent (showList' (map (\(var, n) -> show var <> ": " <> show n) (OccurB.toList $ cmOccurrenceB cm)))
      showOccurrencesU =
        if OccurU.null $ cmOccurrenceU cm
          then ""
          else "  OccruencesU:\n  " <> indent (showList' (map (\(var, n) -> show var <> ": " <> show n) (OccurU.toList $ cmOccurrenceU cm)))

      showMul (aX, bX, cX) = showVecWithParen aX ++ " * " ++ showVecWithParen bX ++ " = " ++ showVec cX
        where
          showVec :: (Show n, Ord n, Eq n, Num n, Show ref) => Either n (PolyG ref n) -> String
          showVec (Left c) = show c
          showVec (Right xs) = show xs

          -- wrap the string with parenthesis if it has more than 1 term
          showVecWithParen :: (Show n, Ord n, Eq n, Num n, Show ref) => PolyG ref n -> String
          showVecWithParen xs =
            let termNumber = case PolyG.view xs of
                  PolyG.Monomial 0 _ -> 1
                  PolyG.Monomial _ _ -> 2
                  PolyG.Binomial 0 _ _ -> 2
                  PolyG.Binomial {} -> 3
                  PolyG.Polynomial 0 xss -> Map.size xss
                  PolyG.Polynomial _ xss -> 1 + Map.size xss
             in if termNumber < 2
                  then showVec (Right xs)
                  else "(" ++ showVec (Right xs) ++ ")"

      showVariables :: String
      showVariables =
        let totalSize = getTotalCount counters
            padRight4 s = s <> replicate (4 - length s) ' '
            padLeft12 n = replicate (12 - length (show n)) ' ' <> show n
            formLine typ =
              padLeft12 (getCount counters (Output, typ))
                <> "    "
                <> padLeft12 (getCount counters (PublicInput, typ))
                <> "    "
                <> padLeft12 (getCount counters (PrivateInput, typ))
                <> "    "
                <> padLeft12 (getCount counters (Intermediate, typ))
            uint w = "\n    UInt" <> padRight4 (toSubscript w) <> formLine (ReadUInt w)
            -- Bit widths existed in the system
            uintWidthEntries (Counters o i p x _ _ _) = IntMap.keysSet (structU o) <> IntMap.keysSet (structU i) <> IntMap.keysSet (structU p) <> IntMap.keysSet (structU x)
            showUInts =
              let entries = uintWidthEntries counters
               in if IntSet.null entries
                    then ""
                    else mconcat $ fmap uint (IntSet.toList entries)
         in if totalSize == 0
              then ""
              else
                "  Variables ("
                  <> show totalSize
                  <> "):\n"
                  <> "                  output       pub input      priv input    intermediate\n"
                  <> "    --------------------------------------------------------------------"
                  <> "\n    Field   "
                  <> formLine ReadField
                  <> "\n    Boolean "
                  <> formLine ReadBool
                  <> showUInts
                  <> "\n"

-------------------------------------------------------------------------------

relocateConstraintModule :: (GaloisField n, Integral n) => ConstraintModule n -> Relocated.RelocatedConstraintSystem n
relocateConstraintModule cm =
  Relocated.RelocatedConstraintSystem
    { Relocated.csField = cmField cm,
      Relocated.csCounters = counters,
      Relocated.csBinReps = binReps,
      Relocated.csBinReps' = map (Seq.fromList . map (first (reindexRefB counters))) (cmBinReps cm),
      Relocated.csConstraints =
        varEqFs
          <> varEqBs
          <> varEqUs
          <> addFs
          <> mulFs,
      Relocated.csEqZeros = toList eqZeros,
      Relocated.csDivMods = divMods,
      Relocated.csModInvs = modInvs
    }
  where
    counters = cmCounters cm
    uncurry3 f (a, b, c) = f a b c

    binReps = generateBinReps counters (cmOccurrenceU cm)

    occurences = constructOccurences cm

    -- \| Generate BinReps from the UIntRelations
    generateBinReps :: Counters -> OccurU -> [BinRep]
    generateBinReps (Counters o i1 i2 _ _ _ _) occurrencesU =
      toList $
        fromSmallCounter Output o
          <> fromSmallCounter PublicInput i1
          <> fromSmallCounter PrivateInput i2
          <> binRepsFromIntermediateRefUsOccurredInUAndF
      where
        intermediateRefUsOccurredInU =
          Set.fromList $
            concatMap
              (\(width, xs) -> mapMaybe (\(var, count) -> if count > 0 then Just (width, var) else Nothing) (IntMap.toList xs))
              (OccurU.toList occurrencesU)

        intermediateRefUsOccurredInBitTests =
          Set.fromList $
            concatMap (\(width, xs) -> map (width,) (IntSet.toList xs)) $
              IntMap.toList (cmBitTests cm)

        binRepsFromIntermediateRefUsOccurredInUAndF =
          Seq.fromList
            $ map
              ( \(width, var) ->
                  let varOffset = reindex counters Intermediate (ReadUInt width) var
                      binRepOffset = reindex counters Intermediate (ReadBits width) var
                   in BinRep varOffset width binRepOffset
              )
            $ Set.toList (intermediateRefUsOccurredInU <> intermediateRefUsOccurredInBitTests)

        -- fromSmallCounter :: VarSort -> SmallCounters -> [BinRep]
        fromSmallCounter sort (Struct _ _ u) = Seq.fromList $ concatMap (fromPair sort) (IntMap.toList u)

        -- fromPair :: VarSort -> (Width, Int) -> [BinRep]
        fromPair sort (width, count) =
          let varOffset = reindex counters sort (ReadUInt width) 0
              binRepOffset = reindex counters sort (ReadBits width) 0
           in [BinRep (varOffset + index) width (binRepOffset + width * index) | index <- [0 .. count - 1]]

    extractFieldRelations :: (GaloisField n, Integral n) => AllRelations n -> Seq (Relocated.Constraint n)
    extractFieldRelations relations =
      let convert :: (GaloisField n, Integral n) => (Ref, Either (n, Ref, n) n) -> Constraint n
          convert (var, Right val) = CVarBindF var val
          convert (var, Left (slope, root, intercept)) =
            case (slope, intercept) of
              (0, _) -> CVarBindF var intercept
              (1, 0) -> CVarEq var root
              (_, _) -> case PolyG.build intercept [(var, -1), (root, slope)] of
                Left _ -> error "[ panic ] extractFieldRelations: failed to build polynomial"
                Right poly -> CAddF poly

          result = map convert $ Map.toList $ AllRelations.toInt shouldBeKept relations
       in Seq.fromList (map (fromConstraint counters) result)

    shouldBeKept :: Ref -> Bool
    shouldBeKept (F ref) = refFShouldBeKept ref
    shouldBeKept (B ref) = refBShouldBeKept ref
    shouldBeKept (U ref) = refUShouldBeKept ref

    refFShouldBeKept :: RefF -> Bool
    refFShouldBeKept ref = case ref of
      RefFX var ->
        -- it's a Field intermediate variable that occurs in the circuit
        var `IntSet.member` refFsInOccurrencesF occurences
      _ ->
        -- it's a pinned Field variable
        True

    refUShouldBeKept :: RefU -> Bool
    refUShouldBeKept ref = case ref of
      RefUX width var ->
        -- it's a UInt intermediate variable that occurs in the circuit
        ( case IntMap.lookup width (refUsInOccurrencesU occurences) of
            Nothing -> False
            Just xs -> IntSet.member var xs
        )
          || ( case IntMap.lookup width (cmBitTests cm) of
                 Nothing -> False
                 Just xs -> IntSet.member var xs
             )
      _ ->
        -- it's a pinned UInt variable
        True

    refBShouldBeKept :: RefB -> Bool
    refBShouldBeKept ref = case ref of
      RefBX var ->
        --  it's a Boolean intermediate variable that occurs in the circuit
        var `IntSet.member` refBsInOccurrencesB occurences
      -- \|| RefBX var `Set.member` refBsInOccurrencesF occurences
      RefUBit _ var _ ->
        --  it's a Bit test of a UInt intermediate variable that occurs in the circuit
        --  the UInt variable should be kept
        shouldBeKept (U var)
      _ ->
        -- it's a pinned Field variable
        True

    extractBooleanRelations :: (GaloisField n, Integral n) => BooleanRelations -> Seq (Relocated.Constraint n)
    extractBooleanRelations relations =
      let convert :: (GaloisField n, Integral n) => (RefB, Either (Bool, RefB) Bool) -> Constraint n
          convert (var, Right val) = CVarBindB var val
          convert (var, Left (dontFlip, root)) =
            if dontFlip
              then CVarEqB var root
              else CVarNEqB var root

          result = map convert $ Map.toList $ BooleanRelations.toMap refBShouldBeKept relations
       in Seq.fromList (map (fromConstraint counters) result)

    extractUIntRelations :: (GaloisField n, Integral n) => UIntRelations n -> Seq (Relocated.Constraint n)
    extractUIntRelations relations =
      let convert :: (GaloisField n, Integral n) => (RefU, Either (Int, RefU) n) -> Constraint n
          convert (var, Right val) = CVarBindU var val
          convert (var, Left (rotation, root)) =
            if rotation == 0
              then CVarEqU var root
              else error "[ panic ] Unexpected rotation in extractUIntRelations"

          result = map convert $ Map.toList $ UIntRelations.toMap refUShouldBeKept relations
       in Seq.fromList (map (fromConstraint counters) result)

    -- varEqFs = fromFieldRelations (cmFieldRelations cm) (FieldRelations.exportUIntRelations (cmFieldRelations cm)) (cmOccurrenceF cm)
    varEqFs = extractFieldRelations (cmFieldRelations cm)
    varEqUs = extractUIntRelations (FieldRelations.exportUIntRelations (cmFieldRelations cm))
    varEqBs = extractBooleanRelations (FieldRelations.exportBooleanRelations (cmFieldRelations cm))

    addFs = Seq.fromList $ map (fromConstraint counters . CAddF) $ cmAddF cm
    mulFs = Seq.fromList $ map (fromConstraint counters . uncurry3 CMulF) $ cmMulF cm
    eqZeros = Seq.fromList $ map (bimap (fromPoly_ counters) (reindexRefF counters)) $ cmEqZeros cm

    divMods = map (\(a, b, q, r) -> (left (reindexRefU counters) a, left (reindexRefU counters) b, left (reindexRefU counters) q, left (reindexRefU counters) r)) $ cmDivMods cm
    modInvs = map (\(a, n, p) -> (left (reindexRefU counters) a, left (reindexRefU counters) n, p)) $ cmModInvs cm

-- | TODO: revisit this
sizeOfConstraintModule :: ConstraintModule n -> Int
sizeOfConstraintModule cm =
  FieldRelations.size (cmFieldRelations cm)
    + BooleanRelations.size (FieldRelations.exportBooleanRelations (cmFieldRelations cm))
    + UIntRelations.size (FieldRelations.exportUIntRelations (cmFieldRelations cm))
    + length (cmAddF cm)
    + length (cmMulF cm)
    + length (cmEqZeros cm)

class UpdateOccurrences ref where
  addOccurrences :: Set ref -> ConstraintModule n -> ConstraintModule n
  removeOccurrences :: Set ref -> ConstraintModule n -> ConstraintModule n

instance UpdateOccurrences Ref where
  addOccurrences =
    flip
      ( foldl
          ( \cm ref ->
              case ref of
                F refF -> addOccurrences (Set.singleton refF) cm
                B refB -> addOccurrences (Set.singleton refB) cm
                U refU -> addOccurrences (Set.singleton refU) cm
          )
      )
  removeOccurrences =
    flip
      ( foldl
          ( \cm ref ->
              case ref of
                F refF -> removeOccurrences (Set.singleton refF) cm
                B refB -> removeOccurrences (Set.singleton refB) cm
                U refU -> removeOccurrences (Set.singleton refU) cm
          )
      )

instance UpdateOccurrences RefF where
  addOccurrences =
    flip
      ( foldl
          ( \cm ref ->
              case ref of
                RefFX var ->
                  cm
                    { cmOccurrenceF = OccurF.increase var (cmOccurrenceF cm)
                    }
                _ -> cm
          )
      )
  removeOccurrences =
    flip
      ( foldl
          ( \cm ref ->
              case ref of
                RefFX var ->
                  cm
                    { cmOccurrenceF = OccurF.decrease var (cmOccurrenceF cm)
                    }
                _ -> cm
          )
      )

instance UpdateOccurrences RefB where
  addOccurrences =
    flip
      ( foldl
          ( \cm ref ->
              case ref of
                RefUBit _ (RefUX width var) _ ->
                  cm
                    { cmOccurrenceU = OccurU.increase width var (cmOccurrenceU cm)
                    }
                RefBX var ->
                  cm
                    { cmOccurrenceB = OccurB.increase var (cmOccurrenceB cm)
                    }
                _ -> cm
          )
      )
  removeOccurrences =
    flip
      ( foldl
          ( \cm ref ->
              case ref of
                RefUBit _ (RefUX width var) _ ->
                  cm
                    { cmOccurrenceU = OccurU.decrease width var (cmOccurrenceU cm)
                    }
                RefBX var ->
                  cm
                    { cmOccurrenceB = OccurB.decrease var (cmOccurrenceB cm)
                    }
                _ -> cm
          )
      )

instance UpdateOccurrences RefU where
  addOccurrences =
    flip
      ( foldl
          ( \cm ref ->
              case ref of
                RefUX width var ->
                  cm
                    { cmOccurrenceU = OccurU.increase width var (cmOccurrenceU cm)
                    }
                _ -> cm
          )
      )
  removeOccurrences =
    flip
      ( foldl
          ( \cm ref ->
              case ref of
                RefUX width var ->
                  cm
                    { cmOccurrenceU = OccurU.decrease width var (cmOccurrenceU cm)
                    }
                _ -> cm
          )
      )

-------------------------------------------------------------------------------

-- | Allow us to determine which relations should be extracted from the pool
data Occurences = Occurences
  { refFsInOccurrencesF :: !IntSet,
    refBsInOccurrencesB :: !IntSet,
    refUsInOccurrencesU :: !(IntMap IntSet)
  }

-- | Smart constructor for 'Occurences'
constructOccurences :: ConstraintModule n -> Occurences
constructOccurences cm =
  Occurences
    { refFsInOccurrencesF = OccurF.occuredSet (cmOccurrenceF cm),
      refBsInOccurrencesB = OccurB.occuredSet (cmOccurrenceB cm),
      refUsInOccurrencesU = OccurU.occuredSet (cmOccurrenceU cm)
    }
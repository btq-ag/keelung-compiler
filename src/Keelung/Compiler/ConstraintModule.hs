{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Keelung.Compiler.ConstraintModule
  ( ConstraintModule (..),
    sizeOfConstraintModule,
    prettyVariables,
    getBooleanConstraintCount,
    UpdateOccurrences (..),
  )
where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map.Strict qualified as Map
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
import Keelung.Compiler.Relations.Boolean qualified as BooleanRelations
import Keelung.Compiler.Relations.Field (AllRelations)
import Keelung.Compiler.Relations.Field qualified as FieldRelations
import Keelung.Compiler.Util (indent)
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Data.Struct
import Keelung.Data.VarGroup (showList', toSubscript)
import Keelung.Field (FieldType)
import Keelung.Syntax.Counters hiding (getBooleanConstraintCount, getBooleanConstraintRanges, prettyBooleanConstraints, prettyVariables)

--------------------------------------------------------------------------------

-- | A constraint module is a collection of constraints with some additional information
data ConstraintModule n = ConstraintModule
  { cmField :: (FieldType, Int, Integer, Integer),
    -- | the minimal bits required to represent a field element
    cmFieldWidth :: Int,
    cmCounters :: !Counters,
    -- for counting the occurrences of variables in constraints (excluding the ones that are in FieldRelations)
    cmOccurrenceF :: !OccurF,
    cmOccurrenceB :: !OccurB,
    cmOccurrenceU :: !OccurU,
    cmFieldRelations :: AllRelations n,
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
    cmModInvs :: [(Either RefU n, Either RefU n, Either RefU n, Integer)]
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
      <> prettyVariables (cmCounters cm)
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
          else "  ModInv hints:\n" <> indent (indent (showList' (map (\(a, _aainv, _n, p) -> show a <> "⁻¹ = (mod " <> show p <> ")") (cmModInvs cm))))

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

prettyVariables :: Counters -> String
prettyVariables counters =
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

-- | Variables that needed to be constrained to be Boolean
--    1. Boolean output variables
--    2. UInt BinReps output variables
--    3. Boolean private input variables
--    4. UInt BinReps private input variables
--    5. Boolean public input variables
--    6. UInt BinReps public input variables
--    7. Boolean intermediate variables
--    8. UInt BinReps public intermediate variables
booleanConstraintCategories :: [(Category, ReadType)]
booleanConstraintCategories =
  [ (Output, ReadBool),
    (Output, ReadAllUInt),
    (PublicInput, ReadBool),
    (PublicInput, ReadAllUInt),
    (PrivateInput, ReadBool),
    (PrivateInput, ReadAllUInt),
    (Intermediate, ReadBool),
    (Intermediate, ReadAllUInt)
  ]

getBooleanConstraintCount :: Counters -> Int
getBooleanConstraintCount counters = sum $ map (getCount counters) booleanConstraintCategories

getBooleanConstraintRanges :: Counters -> [(Int, Int)]
getBooleanConstraintRanges counters = IntMap.toList $ getRanges counters booleanConstraintCategories

prettyBooleanConstraints :: Counters -> [String]
prettyBooleanConstraints counters =
  concatMap showSegment (getBooleanConstraintRanges counters)
  where
    showSegment :: (Int, Int) -> [String]
    showSegment (start, end) =
      case end - start of
        0 -> []
        1 -> [showBooleanConstraint start]
        2 ->
          [ showBooleanConstraint start,
            showBooleanConstraint (start + 1)
          ]
        3 ->
          [ showBooleanConstraint start,
            showBooleanConstraint (start + 1),
            showBooleanConstraint (start + 2)
          ]
        _ ->
          [ showBooleanConstraint start,
            "  ...",
            showBooleanConstraint (end - 1)
          ]

    showBooleanConstraint :: Int -> String
    showBooleanConstraint n = "$" <> show n <> " = $" <> show n <> " * $" <> show n

-------------------------------------------------------------------------------

-- | TODO: revisit this
sizeOfConstraintModule :: ConstraintModule n -> Int
sizeOfConstraintModule cm =
  FieldRelations.size (cmFieldRelations cm)
    + BooleanRelations.size (FieldRelations.exportBooleanRelations (cmFieldRelations cm))
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
          )
      )
  removeOccurrences =
    flip
      ( foldl
          ( \cm ref ->
              case ref of
                F refF -> removeOccurrences (Set.singleton refF) cm
                B refB -> removeOccurrences (Set.singleton refB) cm
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

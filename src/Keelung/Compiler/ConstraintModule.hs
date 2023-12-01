{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Keelung.Compiler.ConstraintModule
  ( ConstraintModule (..),
    sizeOfConstraintModule,
    prettyVariables,
    getBooleanConstraintCount,
    UpdateOccurrences (..),
    addOccurrencesTuple,
    removeOccurrencesTuple,
  )
where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung.Compiler.Optimize.OccurB (OccurB)
import Keelung.Compiler.Optimize.OccurB qualified as OccurB
import Keelung.Compiler.Optimize.OccurF (OccurF)
import Keelung.Compiler.Optimize.OccurF qualified as OccurF
import Keelung.Compiler.Optimize.OccurU (OccurU)
import Keelung.Compiler.Optimize.OccurU qualified as OccurU
import Keelung.Compiler.Optimize.OccurUB (OccurUB)
import Keelung.Compiler.Optimize.OccurUB qualified as OccurUB
import Keelung.Compiler.Relations (Relations)
import Keelung.Compiler.Relations qualified as Relations
import Keelung.Compiler.Util
import Keelung.Data.FieldInfo
import Keelung.Data.Limb (Limb (..))
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.Struct
import Keelung.Data.U (U)
import Keelung.Syntax.Counters hiding (getBooleanConstraintCount, getBooleanConstraintRanges, prettyBooleanConstraints, prettyVariables)

--------------------------------------------------------------------------------

-- | A constraint module is a collection of constraints with some additional information
data ConstraintModule n = ConstraintModule
  { cmField :: FieldInfo,
    cmCounters :: !Counters,
    -- for counting the occurrences of variables in constraints (excluding the ones that are in Relations)
    cmOccurrenceF :: !OccurF,
    cmOccurrenceB :: !OccurB,
    cmOccurrenceU :: !OccurU,
    cmOccurrenceUB :: !OccurUB,
    cmRelations :: Relations n,
    -- addative constraints
    cmAddL :: [PolyL n],
    -- multiplicative constraints
    cmMulL :: [(PolyL n, PolyL n, Either n (PolyL n))],
    -- hits for computing equality
    cmEqZeros :: [(PolyL n, RefF)],
    -- hints for generating witnesses for DivMod constraints
    -- a = b * q + r
    cmDivMods :: [(Either RefU U, Either RefU U, Either RefU U, Either RefU U)],
    -- hints for generating witnesses for carry-less DivMod constraints
    -- a = b .*. q .^. r
    cmCLDivMods :: [(Either RefU U, Either RefU U, Either RefU U, Either RefU U)],
    -- hints for generating witnesses for ModInv constraints
    cmModInvs :: [(Either RefU U, Either RefU U, Either RefU U, U)]
  }
  deriving (Eq, Generic, NFData)

instance (GaloisField n, Integral n) => Show (ConstraintModule n) where
  show cm =
    "Constraint Module {\n"
      <> showFieldInfo
      <> showVarEqF
      <> showAddL
      <> showMulL
      <> showEqs
      <> showBooleanConstraints
      <> showDivModHints
      <> showCLDivModHints
      <> showModInvHints
      <> show (cmOccurrenceF cm)
      <> show (cmOccurrenceB cm)
      <> show (cmOccurrenceU cm)
      <> show (cmOccurrenceUB cm)
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

      showFieldInfo :: String
      showFieldInfo = "  Field: " <> show (fieldTypeData (cmField cm)) <> "\n"

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

      showCLDivModHints =
        if null $ cmCLDivMods cm
          then ""
          else "  CLDivMod hints:\n" <> indent (indent (showList' (map (\(x, y, q, r) -> show x <> " = " <> show y <> " * " <> show q <> " + " <> show r) (cmCLDivMods cm))))

      showModInvHints =
        if null $ cmModInvs cm
          then ""
          else "  ModInv hints:\n" <> indent (indent (showList' (map (\(a, _aainv, _n, p) -> show a <> "⁻¹ = (mod " <> show p <> ")") (cmModInvs cm))))

      showVarEqF =
        if Relations.size (cmRelations cm) == 0
          then ""
          else "  Relations:\n" <> indent (indent (show (cmRelations cm)))

      showAddL = adapt "AddL" (cmAddL cm) $ \xs -> "0 = " <> show xs
      showMulL = adapt "MulL" (cmMulL cm) showMulL'

      showEqs = adapt "EqZeros" (cmEqZeros cm) $ \(poly, m) ->
        "EqZeros " <> show poly <> " / " <> show m

      showMulL' (aX, bX, cX) = showVecWithParen aX ++ " * " ++ showVecWithParen bX ++ " = " ++ showVec cX
        where
          showVec :: (Eq n, Num n, Ord n, Show n) => Either n (PolyL n) -> String
          showVec (Left c) = show c
          showVec (Right xs) = show xs

          -- wrap the string with parenthesis if it has more than 1 term
          showVecWithParen :: (Eq n, Num n, Ord n, Show n) => PolyL n -> String
          showVecWithParen xs =
            if PolyL.size xs < 2
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
      uWidthEntries (Counters o i p x _ _) = IntMap.keysSet (structU o) <> IntMap.keysSet (structU i) <> IntMap.keysSet (structU p) <> IntMap.keysSet (structU x)
      showUInts =
        let entries = uWidthEntries counters
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
    (Output, ReadAllUInts),
    (PublicInput, ReadBool),
    (PublicInput, ReadAllUInts),
    (PrivateInput, ReadBool),
    (PrivateInput, ReadAllUInts),
    (Intermediate, ReadBool),
    (Intermediate, ReadAllUInts)
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
  Relations.size (cmRelations cm)
    + length (cmAddL cm)
    + length (cmMulL cm)
    + length (cmEqZeros cm)
    + length (cmDivMods cm)
    + length (cmModInvs cm)

class UpdateOccurrences ref where
  addOccurrences :: Set ref -> ConstraintModule n -> ConstraintModule n
  removeOccurrences :: Set ref -> ConstraintModule n -> ConstraintModule n

addOccurrencesTuple :: (GaloisField n, Integral n) => (Set RefU, Set Ref) -> ConstraintModule n -> ConstraintModule n
addOccurrencesTuple (ls, vars) = addOccurrences ls . addOccurrences vars

removeOccurrencesTuple :: (GaloisField n, Integral n) => (Set RefU, Set Ref) -> ConstraintModule n -> ConstraintModule n
removeOccurrencesTuple (ls, vars) = addOccurrences ls . addOccurrences vars

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

instance UpdateOccurrences Limb where
  addOccurrences =
    flip
      ( foldl
          ( \cm limb ->
              case lmbRef limb of
                RefUX width var ->
                  cm
                    { cmOccurrenceUB = OccurUB.increase width var (lmbOffset limb, lmbOffset limb + lmbWidth limb) (cmOccurrenceUB cm)
                    }
                _ -> cm
          )
      )
  removeOccurrences =
    flip
      ( foldl
          ( \cm limb ->
              case lmbRef limb of
                RefUX width var ->
                  cm
                    { cmOccurrenceUB = OccurUB.decrease width var (lmbOffset limb, lmbOffset limb + lmbWidth limb) (cmOccurrenceUB cm)
                    }
                _ -> cm
          )
      )
  -- addOccurrences = addOccurrences . Set.map Limb.lmbRef
  -- removeOccurrences = removeOccurrences . Set.map Limb.lmbRef

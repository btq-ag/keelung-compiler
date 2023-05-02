{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use lambda-case" #-}

module Keelung.Compiler.ConstraintSystem
  ( ConstraintSystem (..),
    relocateConstraintSystem,
    sizeOfConstraintSystem,
    UpdateOccurrences (..),
  )
where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Relations.Boolean (BooleanRelations)
import Keelung.Compiler.Compile.Relations.Boolean qualified as BooleanRelations
import Keelung.Compiler.Compile.Relations.Field (AllRelations)
import Keelung.Compiler.Compile.Relations.Field qualified as AllRelations
import Keelung.Compiler.Compile.Relations.Field qualified as FieldRelations
import Keelung.Compiler.Compile.Relations.UInt (UIntRelations)
import Keelung.Compiler.Compile.Relations.UInt qualified as UIntRelations
import Keelung.Compiler.Constraint
import Keelung.Compiler.Relocated qualified as Relocated
import Keelung.Compiler.Util (indent)
import Keelung.Constraint.R1CS qualified as Constraint
import Keelung.Data.BinRep (BinRep (..))
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Data.Struct
import Keelung.Data.VarGroup (showList', toSubscript)
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

-- | A constraint system is a collection of constraints
data ConstraintSystem n = ConstraintSystem
  { csCounters :: !Counters,
    csUseNewOptimizer :: Bool,
    -- for counting the occurences of variables in constraints (excluding the ones that are in FieldRelations)
    csOccurrenceF :: !(Map Ref Int),
    csOccurrenceB :: !(Map RefB Int),
    csOccurrenceU :: !(Map RefU Int),
    -- when x == y (FieldRelations)
    csFieldRelations :: AllRelations n,
    -- csUIntRelations :: UIntRelations n,
    -- addative constraints
    csAddF :: [PolyG Ref n],
    -- multiplicative constraints
    csMulF :: [(PolyG Ref n, PolyG Ref n, Either n (PolyG Ref n))],
    -- constraints for computing equality
    csNEqF :: Map (RefT, RefT) RefT,
    csNEqU :: Map (RefU, RefU) RefT,
    -- hints for generating witnesses for DivMod constraints
    csDivMods :: [(RefU, RefU, RefU, RefU)],
    -- hints for generating witnesses for ModInv constraints
    csModInvs :: [(RefU, RefU, Integer)]
  }
  deriving (Eq, Generic, NFData)

instance (GaloisField n, Integral n) => Show (ConstraintSystem n) where
  show cs =
    "Constraint Module {\n"
      <> showVarEqF
      -- <> showVarEqU
      <> showAddF
      <> showMulF
      <> showNEqF
      <> showNEqU
      <> showBooleanConstraints
      <> showDivModHints
      <> showModInvHints
      <> showOccurrencesF
      <> showOccurrencesB
      <> showOccurrencesU
      <> showVariables
      <> "}"
    where
      counters = csCounters cs
      -- sizes of constraint groups
      booleanConstraintSize = getBooleanConstraintSize counters

      adapt :: String -> [a] -> (a -> String) -> String
      adapt name xs f =
        let size = length xs
         in if size == 0
              then ""
              else "  " <> name <> " (" <> show size <> "):\n\n" <> unlines (map (("    " <>) . f) xs) <> "\n"

      -- Boolean constraints
      showBooleanConstraints =
        if booleanConstraintSize == 0
          then ""
          else
            "  Boolean constriants ("
              <> show booleanConstraintSize
              <> "):\n\n"
              <> unlines (map ("    " <>) (prettyBooleanConstraints counters))
              <> "\n"

      showDivModHints =
        if null $ csDivMods cs
          then ""
          else "  DivMod hints:\n" <> indent (indent (showList' (map (\(x, y, q, r) -> show x <> " = " <> show y <> " * " <> show q <> " + " <> show r) (csDivMods cs))))

      showModInvHints =
        if null $ csModInvs cs
          then ""
          else "  ModInv hints:\n" <> indent (indent (showList' (map (\(x, _n, p) -> show x <> "⁻¹ = (mod " <> show p <> ")") (csModInvs cs))))

      -- BinRep constraints
      -- showBinRepConstraints =
      --   if totalBinRepConstraintSize == 0
      --     then ""
      --     else
      --       "  Binary representation constriants ("
      --         <> show totalBinRepConstraintSize
      --         <> "):\n\n"
      --         <> unlines (map ("    " <>) (prettyBinRepConstraints counters))
      --         <> "\n"

      showVarEqF = "  Field relations:\n" <> indent (indent (show (csFieldRelations cs)))
      -- showVarEqU = "  UInt relations:\n" <> indent (indent (show (csUIntRelations cs)))

      showAddF = adapt "AddF" (csAddF cs) show

      showMulF = adapt "MulF" (csMulF cs) showMul

      showNEqF = adapt "NEqF" (Map.toList $ csNEqF cs) $ \((x, y), m) -> "NEqF " <> show x <> " " <> show y <> " " <> show m
      showNEqU = adapt "NEqU" (Map.toList $ csNEqU cs) $ \((x, y), m) -> "NEqF " <> show x <> " " <> show y <> " " <> show m

      showOccurrencesF =
        if Map.null $ csOccurrenceF cs
          then ""
          else "  OccruencesF:\n  " <> indent (showList' (map (\(var, n) -> show var <> ": " <> show n) (Map.toList $ csOccurrenceF cs)))
      showOccurrencesB =
        if Map.null $ csOccurrenceB cs
          then ""
          else "  OccruencesB:\n  " <> indent (showList' (map (\(var, n) -> show var <> ": " <> show n) (Map.toList $ csOccurrenceB cs)))
      showOccurrencesU =
        if Map.null $ csOccurrenceU cs
          then ""
          else "  OccruencesU:\n  " <> indent (showList' (map (\(var, n) -> show var <> ": " <> show n) (Map.toList $ csOccurrenceU cs)))

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
              padLeft12 (getCount OfOutput typ counters)
                <> "    "
                <> padLeft12 (getCount OfPublicInput typ counters)
                <> "    "
                <> padLeft12 (getCount OfPrivateInput typ counters)
                <> "    "
                <> padLeft12 (getCount OfIntermediate typ counters)
            uint w = "\n    UInt" <> padRight4 (toSubscript w) <> formLine (OfUInt w)
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
                  <> formLine OfField
                  <> "\n    Boolean "
                  <> formLine OfBoolean
                  <> showUInts
                  <> "\n"

-------------------------------------------------------------------------------

relocateConstraintSystem :: (GaloisField n, Integral n) => ConstraintSystem n -> Relocated.RelocatedConstraintSystem n
relocateConstraintSystem cs =
  Relocated.RelocatedConstraintSystem
    { Relocated.csUseNewOptimizer = csUseNewOptimizer cs,
      Relocated.csCounters = counters,
      Relocated.csBinReps = binReps,
      Relocated.csConstraints =
        varEqFs
          <> varEqBs
          <> varEqUs
          <> addFs
          <> mulFs
          <> nEqFs
          <> nEqUs,
      Relocated.csDivMods = divMods,
      Relocated.csModInvs = modDivs
    }
  where
    counters = csCounters cs
    uncurry3 f (a, b, c) = f a b c

    binReps = generateBinReps counters (csOccurrenceU cs) (csOccurrenceF cs)

    memberships = constructMemberships cs

    -- \| Generate BinReps from the UIntRelations
    generateBinReps :: Counters -> Map RefU Int -> Map Ref Int -> [BinRep]
    generateBinReps (Counters o i1 i2 _ _ _ _) occurrencesU occurrencesF =
      toList $
        fromSmallCounter OfOutput o
          <> fromSmallCounter OfPublicInput i1
          <> fromSmallCounter OfPrivateInput i2
          <> binRepsFromIntermediateRefUsOccurredInUAndF
      where
        intermediateRefUsOccurredInU =
          Set.fromList $
            Map.elems $
              Map.mapMaybeWithKey
                ( \ref count -> case ref of
                    RefUX width var -> if count > 0 then Just (width, var) else Nothing
                    _ -> Nothing
                )
                occurrencesU

        intermediateRefUsOccurredInF =
          Set.fromList $
            Map.elems $
              Map.mapMaybeWithKey
                ( \ref count -> case ref of
                    U (RefUX width var) -> if count > 0 then Just (width, var) else Nothing
                    _ -> Nothing
                )
                occurrencesF

        binRepsFromIntermediateRefUsOccurredInUAndF =
          Seq.fromList
            $ map
              ( \(width, var) ->
                  let varOffset = reindex counters OfIntermediate (OfUInt width) var
                      binRepOffset = reindex counters OfIntermediate (OfUIntBinRep width) var
                   in BinRep varOffset width binRepOffset
              )
            $ Set.toList (intermediateRefUsOccurredInU <> intermediateRefUsOccurredInF)

        -- binRepsFromIntermediateRefUsOccurredInF =
        --   Seq.fromList $
        --     map
        --       ( \(width, var) ->
        --           let varOffset = reindex counters OfIntermediate (OfUInt width) var
        --               binRepOffset = reindex counters OfIntermediate (OfUIntBinRep width) var
        --            in BinRep varOffset width binRepOffset
        --       )
        --       intermediateRefUsOccurredInF

        -- fromSmallCounter :: VarSort -> SmallCounters -> [BinRep]
        fromSmallCounter sort (Struct _ _ u) = Seq.fromList $ concatMap (fromPair sort) (IntMap.toList u)

        -- fromPair :: VarSort -> (Width, Int) -> [BinRep]
        fromPair sort (width, count) =
          let varOffset = reindex counters sort (OfUInt width) 0
              binRepOffset = reindex counters sort (OfUIntBinRep width) 0
           in [BinRep (varOffset + index) width (binRepOffset + width * index) | index <- [0 .. count - 1]]

    -- fromFieldRelations :: (GaloisField n, Integral n) => AllRelations n -> UIntRelations n -> Map Ref Int -> Seq (Relocated.Constraint n)
    -- fromFieldRelations fieldRels _uintRels occurrencesF =
    --   let outputVars = [F $ RefFO i | i <- [0 .. getCount OfOutput OfField counters - 1]]
    --       publicInputVars = [F $ RefFI i | i <- [0 .. getCount OfPublicInput OfField counters - 1]]
    --       privateInputVars = [F $ RefFP i | i <- [0 .. getCount OfPrivateInput OfField counters - 1]]
    --       occurredInF = Map.keys $ Map.filterWithKey (\ref count -> count > 0 && not (pinnedRef ref)) occurrencesF
    --    in Seq.fromList (Maybe.mapMaybe toConstraint outputVars)
    --         <> Seq.fromList (Maybe.mapMaybe toConstraint publicInputVars)
    --         <> Seq.fromList (Maybe.mapMaybe toConstraint privateInputVars)
    --         <> Seq.fromList (Maybe.mapMaybe toConstraint occurredInF)
    --   where
    --     boolRels = FieldRelations.exportBooleanRelations fieldRels

    --     toConstraint var = case FieldRelations.lookup var fieldRels of
    --       FieldRelations.Root ->
    --         -- var is already a root
    --         Nothing
    --       FieldRelations.Value intercept ->
    --         -- var = intercept
    --         Just $ fromConstraint counters $ CVarBindF var intercept
    --       FieldRelations.ChildOf slope root intercept ->
    --         -- var = slope * root + intercept
    --         case root of
    --           B refB -> case BooleanRelations.lookup refB boolRels of
    --             BooleanRelations.Root -> case PolyG.build intercept [(var, -1), (root, slope)] of
    --               Left _ -> Nothing
    --               Right poly -> Just $ fromConstraint counters $ CAddF poly
    --             BooleanRelations.Value intercept' ->
    --               -- root = intercept'
    --               Just $ fromConstraint counters $ CVarBindF var (slope * (if intercept' then 1 else 0) + intercept)
    --             BooleanRelations.ChildOf polarity root' ->
    --               -- root = polarity * slope * root' + intercept'
    --               case PolyG.build intercept [(var, -1), (B root', (if polarity then 1 else -1) * slope)] of
    --                 Left _ -> Nothing
    --                 Right poly -> Just $ fromConstraint counters $ CAddF poly
    --           _ -> case PolyG.build intercept [(var, -1), (root, slope)] of
    --             Left _ -> Nothing
    --             Right poly -> Just $ fromConstraint counters $ CAddF poly

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

    refFShouldBeKept :: RefT -> Bool
    refFShouldBeKept ref = case ref of
      RefFX var ->
        -- it's a Field intermediate variable that occurs in the circuit
        RefFX var `Set.member` refFsInOccurrencesF memberships
      _ ->
        -- it's a pinned Field variable
        True

    refUShouldBeKept :: RefU -> Bool
    refUShouldBeKept ref = case ref of
      RefUX width var ->
        -- it's a UInt intermediate variable that occurs in the circuit
        RefUX width var `Set.member` refUsInOccurrencesF memberships
          || RefUX width var `Set.member` refUsInOccurrencesU memberships
      _ ->
        -- it's a pinned UInt variable
        True

    refBShouldBeKept :: RefB -> Bool
    refBShouldBeKept ref = case ref of
      RefBX var ->
        --  it's a Boolean intermediate variable that occurs in the circuit
        RefBX var `Set.member` refBsInOccurrencesB memberships
          || RefBX var `Set.member` refBsInOccurrencesF memberships
      RefUBit _ var _ ->
        --  it's a Bit test of a UInt intermediate variable that occurs in the circuit
        --  the UInt variable should be kept
        var `Set.member` bitTestsInOccurrencesB memberships
          || shouldBeKept (U var)
      _ ->
        -- it's a pinned Field variable
        True

    extractBooleanRelations :: (GaloisField n, Integral n) => BooleanRelations -> Seq (Relocated.Constraint n)
    extractBooleanRelations relations =
      let convert :: (GaloisField n, Integral n) => (RefB, Either (Bool, RefB) Bool) -> Constraint n
          convert (var, Right val) = CVarBindB var (if val then 1 else 0)
          convert (var, Left (dontFlip, root)) =
            if dontFlip
              then CVarEqB var root
              else CVarNEqB var root

          result = map convert $ Map.toList $ BooleanRelations.toMap2 refBShouldBeKept relations
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

    -- varEqFs = fromFieldRelations (csFieldRelations cs) (FieldRelations.exportUIntRelations (csFieldRelations cs)) (csOccurrenceF cs)
    varEqFs = extractFieldRelations (csFieldRelations cs)
    varEqUs = extractUIntRelations (FieldRelations.exportUIntRelations (csFieldRelations cs))
    varEqBs = extractBooleanRelations (FieldRelations.exportBooleanRelations (csFieldRelations cs))

    addFs = Seq.fromList $ map (fromConstraint counters . CAddF) $ csAddF cs
    mulFs = Seq.fromList $ map (fromConstraint counters . uncurry3 CMulF) $ csMulF cs
    nEqFs = Seq.fromList $ map (\((x, y), m) -> Relocated.CNEq (Constraint.CNEQ (Left (reindexRefT counters x)) (Left (reindexRefT counters y)) (reindexRefT counters m))) $ Map.toList $ csNEqF cs
    nEqUs = Seq.fromList $ map (\((x, y), m) -> Relocated.CNEq (Constraint.CNEQ (Left (reindexRefU counters x)) (Left (reindexRefU counters y)) (reindexRefT counters m))) $ Map.toList $ csNEqU cs

    divMods = map (\(a, b, q, r) -> (reindexRefU counters a, reindexRefU counters b, reindexRefU counters q, reindexRefU counters r)) $ csDivMods cs
    modDivs = map (\(a, n, p) -> (reindexRefU counters a, reindexRefU counters n, p)) $ csModInvs cs

sizeOfConstraintSystem :: ConstraintSystem n -> Int
sizeOfConstraintSystem cs =
  FieldRelations.size (csFieldRelations cs)
    + BooleanRelations.size (FieldRelations.exportBooleanRelations (csFieldRelations cs))
    + UIntRelations.size (FieldRelations.exportUIntRelations (csFieldRelations cs))
    + length (csAddF cs)
    + length (csMulF cs)
    + length (csNEqF cs)
    + length (csNEqU cs)

class UpdateOccurrences ref where
  addOccurrences :: Set ref -> ConstraintSystem n -> ConstraintSystem n
  removeOccurrences :: Set ref -> ConstraintSystem n -> ConstraintSystem n

instance UpdateOccurrences Ref where
  addOccurrences =
    flip
      ( foldl
          ( \cs ref ->
              case ref of
                B refB ->
                  cs
                    { csOccurrenceB = Map.insertWith (+) refB 1 (csOccurrenceB cs)
                    }
                _ ->
                  cs
                    { csOccurrenceF = Map.insertWith (+) ref 1 (csOccurrenceF cs)
                    }
          )
      )
  removeOccurrences =
    flip
      ( foldl
          ( \cs ref ->
              case ref of
                B refB ->
                  cs
                    { csOccurrenceB = Map.adjust (\count -> pred count `max` 0) refB (csOccurrenceB cs)
                    }
                _ ->
                  cs
                    { csOccurrenceF = Map.adjust (\count -> pred count `max` 0) ref (csOccurrenceF cs)
                    }
          )
      )

instance UpdateOccurrences RefT where
  addOccurrences =
    flip
      ( foldl
          ( \cs ref ->
              cs
                { csOccurrenceF = Map.insertWith (+) (F ref) 1 (csOccurrenceF cs)
                }
          )
      )
  removeOccurrences =
    flip
      ( foldl
          ( \cs ref ->
              cs
                { csOccurrenceF = Map.adjust (\count -> pred count `max` 0) (F ref) (csOccurrenceF cs)
                }
          )
      )

instance UpdateOccurrences RefB where
  addOccurrences =
    flip
      ( foldl
          ( \cs ref ->
              case ref of
                RefUBit _ refU _ ->
                  cs
                    { csOccurrenceU = Map.insertWith (+) refU 1 (csOccurrenceU cs)
                    }
                _ ->
                  cs
                    { csOccurrenceB = Map.insertWith (+) ref 1 (csOccurrenceB cs)
                    }
          )
      )
  removeOccurrences =
    flip
      ( foldl
          ( \cs ref ->
              case ref of
                RefUBit _ refU _ ->
                  cs
                    { csOccurrenceU = Map.adjust (\count -> pred count `max` 0) refU (csOccurrenceU cs)
                    }
                _ ->
                  cs
                    { csOccurrenceB = Map.adjust (\count -> pred count `max` 0) ref (csOccurrenceB cs)
                    }
          )
      )

instance UpdateOccurrences RefU where
  addOccurrences =
    flip
      ( foldl
          ( \cs ref ->
              cs
                { csOccurrenceU = Map.insertWith (+) ref 1 (csOccurrenceU cs)
                }
          )
      )
  removeOccurrences =
    flip
      ( foldl
          ( \cs ref ->
              cs
                { csOccurrenceU = Map.adjust (\count -> pred count `max` 0) ref (csOccurrenceU cs)
                }
          )
      )

-------------------------------------------------------------------------------

data Memberships = Memberships
  { refFsInOccurrencesF :: !(Set RefT),
    refBsInOccurrencesF :: !(Set RefB),
    refUsInOccurrencesF :: !(Set RefU),
    bitTestsInOccurrencesB :: !(Set RefU),
    refBsInOccurrencesB :: !(Set RefB),
    refUsInOccurrencesU :: !(Set RefU)
  }

constructMemberships :: ConstraintSystem n -> Memberships
constructMemberships cs =
  let findFInRef (F _) 0 = Nothing
      findFInRef (F r) _ = Just r
      findFInRef _ _ = Nothing

      findUInRef (U _) 0 = Nothing
      findUInRef (U r) _ = Just r
      findUInRef _ _ = Nothing

      findBitTestInRefB (RefUBit {}) 0 = Nothing
      findBitTestInRefB (RefUBit _ r _) _ = Just r
      findBitTestInRefB _ _ = Nothing

      findBInRef (B _) 0 = Nothing
      findBInRef (B r) _ = Just r
      findBInRef _ _ = Nothing
   in Memberships
        { refFsInOccurrencesF = Set.fromList $ Map.elems $ Map.mapMaybeWithKey findFInRef (csOccurrenceF cs),
          refBsInOccurrencesF = Set.fromList $ Map.elems $ Map.mapMaybeWithKey findBInRef (csOccurrenceF cs),
          refUsInOccurrencesF = Set.fromList $ Map.elems $ Map.mapMaybeWithKey findUInRef (csOccurrenceF cs),
          bitTestsInOccurrencesB = Set.fromList $ Map.elems $ Map.mapMaybeWithKey findBitTestInRefB (csOccurrenceB cs),
          refBsInOccurrencesB = Map.keysSet $ Map.filter (> 0) (csOccurrenceB cs),
          refUsInOccurrencesU = Map.keysSet $ Map.filter (> 0) (csOccurrenceU cs)
        }
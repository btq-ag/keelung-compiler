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
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe qualified as Maybe
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung.Compiler.Constraint
import Keelung.Compiler.Optimize.MinimizeConstraints.BooleanRelations (BooleanRelations)
import Keelung.Compiler.Optimize.MinimizeConstraints.BooleanRelations qualified as BooleanRelations
import Keelung.Compiler.Optimize.MinimizeConstraints.FieldRelations (FieldRelations)
import Keelung.Compiler.Optimize.MinimizeConstraints.FieldRelations qualified as FieldRelations
import Keelung.Compiler.Optimize.MinimizeConstraints.UIntRelations (UIntRelations)
import Keelung.Compiler.Optimize.MinimizeConstraints.UIntRelations qualified as UIntRelations
import Keelung.Compiler.Relocated qualified as Relocated
import Keelung.Compiler.Util (indent)
import Keelung.Constraint.R1CS qualified as Constraint
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Data.Struct
import Keelung.Data.VarGroup (showList', toSubscript)
import Keelung.Syntax.Counters
import Debug.Trace

--------------------------------------------------------------------------------

-- | A constraint system is a collection of constraints
data ConstraintSystem n = ConstraintSystem
  { csCounters :: !Counters,
    csUseNewOptimizer :: Bool,
    -- for counting the occurences of variables in constraints (excluding the ones that are in FieldRelations)
    csOccurrenceF :: !(Map RefF Int),
    csOccurrenceB :: !(Map RefB Int),
    csOccurrenceU :: !(Map RefU Int),
    -- when x == y (FieldRelations)
    csFieldRelations :: FieldRelations n,
    csUIntRelations :: UIntRelations n,
    -- addative constraints
    csAddF :: [PolyG RefF n],
    -- multiplicative constraints
    csMulF :: [(PolyG RefF n, PolyG RefF n, Either n (PolyG RefF n))],
    -- constraints for computing equality
    csNEqF :: Map (RefF, RefF) RefF,
    csNEqU :: Map (RefU, RefU) RefU
  }
  deriving (Eq, Generic, NFData)

instance (GaloisField n, Integral n) => Show (ConstraintSystem n) where
  show cs =
    "Constraint Module {\n"
      <> showVarEqF
      <> showVarEqU
      <> showAddF
      <> showMulF
      <> showNEqF
      <> showNEqU
      <> showBooleanConstraints
      <> showBinRepConstraints
      <> showOccurrencesF
      <> showOccurrencesB
      <> showOccurrencesU
      <> showVariables
      <> "}"
    where
      counters = csCounters cs
      -- sizes of constraint groups
      totalBinRepConstraintSize = getBinRepConstraintSize counters
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

      -- BinRep constraints
      showBinRepConstraints =
        if totalBinRepConstraintSize == 0
          then ""
          else
            "  Binary representation constriants ("
              <> show totalBinRepConstraintSize
              <> "):\n\n"
              <> unlines (map ("    " <>) (prettyBinRepConstraints counters))
              <> "\n"

      showVarEqF = "  Field relations:\n" <> indent (indent (show (csFieldRelations cs)))
      showVarEqU = "  UInt relations:\n" <> indent (indent (show (csUIntRelations cs)))

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

relocateConstraintSystem :: (GaloisField n, Integral n) => ConstraintSystem n -> Relocated.RelocatedConstraintSystem n
relocateConstraintSystem cs =
  Relocated.RelocatedConstraintSystem
    { Relocated.csCounters = counters,
      Relocated.csConstraints =
        varEqFs
          <> varEqUs
          <> addFs
          <> mulFs
          <> nEqFs
          <> nEqUs
    }
  where
    counters = csCounters cs
    uncurry3 f (a, b, c) = f a b c

    fromFieldRelations :: (GaloisField n, Integral n) => FieldRelations n -> UIntRelations n -> Map RefF Int -> Map RefB Int -> Map RefU Int -> Seq (Relocated.Constraint n)
    fromFieldRelations fieldRels _uintRels occurrencesF occurrencesB occurrencesU =
      let outputVars = [RefFO i | i <- [0 .. getCount OfOutput OfField counters - 1]]
          publicInputVars = [RefFI i | i <- [0 .. getCount OfPublicInput OfField counters - 1]]
          privateInputVars = [RefFP i | i <- [0 .. getCount OfPrivateInput OfField counters - 1]]
          occurredInF = Map.keys $ Map.filterWithKey (\ref count -> count > 0 && not (pinnedRefF ref)) occurrencesF
       in Seq.fromList
            (Maybe.mapMaybe toConstraint outputVars)
            <> Seq.fromList (Maybe.mapMaybe toConstraint publicInputVars)
            <> Seq.fromList (Maybe.mapMaybe toConstraint privateInputVars)
            <> Seq.fromList (Maybe.mapMaybe toConstraint occurredInF)
            <> fromBooleanRelations boolRels occurrencesF occurrencesB occurrencesU
      where
        boolRels = FieldRelations.exportBooleanRelations fieldRels

        toConstraint var = case FieldRelations.parentOf fieldRels var of
          FieldRelations.Root ->
            -- var is already a root
            Nothing
          FieldRelations.Constant intercept ->
            -- var = intercept
            Just $ fromConstraint counters $ CVarBindF var intercept
          FieldRelations.ChildOf slope root intercept ->
            -- var = slope * root + intercept
            case root of
              RefBtoRefF refB -> case BooleanRelations.lookup boolRels refB of
                BooleanRelations.Root -> case PolyG.build intercept [(var, -1), (root, slope)] of
                  Left _ -> Nothing
                  Right poly -> Just $ fromConstraint counters $ CAddF poly
                BooleanRelations.Constant intercept' ->
                  -- root = intercept'
                  Just $ fromConstraint counters $ CVarBindF var (slope * (if intercept' then 1 else 0) + intercept)
                BooleanRelations.ChildOf slope' root' ->
                  -- root = slope' * root' + intercept'
                  case PolyG.build intercept [(var, -1), (RefBtoRefF root', (if slope' then 1 else -1) * slope)] of
                    Left _ -> Nothing
                    Right poly -> Just $ fromConstraint counters $ CAddF poly
              _ -> case PolyG.build intercept [(var, -1), (root, slope)] of
                Left _ -> Nothing
                Right poly -> Just $ fromConstraint counters $ CAddF poly

    fromBooleanRelations :: (GaloisField n, Integral n) => BooleanRelations -> Map RefF Int -> Map RefB Int -> Map RefU Int -> Seq (Relocated.Constraint n)
    fromBooleanRelations relations occurrencesF occurrencesB occurrencesU =
      let -- outputVars = [RefBO i | i <- [0 .. getCount OfOutput OfBoolean counters - 1]]
          -- publicInputVars = [RefBI i | i <- [0 .. getCount OfPublicInput OfBoolean counters - 1]]
          -- privateInputVars = [RefBP i | i <- [0 .. getCount OfPrivateInput OfBoolean counters - 1]]
          -- occurredInB = Map.keys $ Map.filter (> 0) occurrencesB

          -- findRefBInRefF (RefBtoRefF _) 0 = Nothing
          -- findRefBInRefF (RefBtoRefF r) _ = Just r
          -- findRefBInRefF _ _ = Nothing

          -- findRefBInRefU (RefBtoRefU _) 0 = Nothing
          -- findRefBInRefU (RefBtoRefU r) _ = Just r
          -- findRefBInRefU _ _ = Nothing

          -- occurredInF = Map.elems $ Map.mapMaybeWithKey findRefBInRefF occurrencesF

          -- | Export of UInt-related constriants
          refUsOccurredInF = Set.fromList $ Map.elems $ Map.mapMaybeWithKey findRefUValInRefF occurrencesF
          findRefUValInRefF (RefUVal _) 0 = Nothing
          findRefUValInRefF (RefUVal r) _ = Just r
          findRefUValInRefF _ _ = Nothing

          refUsOccurredInB = Set.fromList $ Map.elems $ Map.mapMaybeWithKey findBitTestInRefB occurrencesB
          findBitTestInRefB (RefUBit {}) 0 = Nothing
          findBitTestInRefB (RefUBit _ ref _) _ = Just ref
          findBitTestInRefB _ _ = Nothing

          refUsOccurredInU = Set.fromList $ Map.elems $ Map.mapMaybeWithKey findRefBInRefU occurrencesU
          findRefBInRefU (RefBtoRefU _) 0 = Nothing
          findRefBInRefU (RefBtoRefU r) _ = Just r
          findRefBInRefU _ _ = Nothing

          -- occurredBitTests =
          --   Set.filter
          --     ( \refB ->
          --         case refB of
          --           RefUBit _ ref _ -> ref `Set.member` refUsOccurredInF || ref `Set.member` refUsOccurredInB || pinnedRefU ref
          --           _ -> False
          --     )
          --     (BooleanRelations.exportPinnedBitTests relations)

          shouldKeep :: RefB -> Bool
          shouldKeep (RefB ref) = RefB ref `Set.member` Map.keysSet (Map.filter (> 0) occurrencesB) || RefB ref `Set.member` refUsOccurredInU
          shouldKeep (RefUBit _ ref _) = ref `Set.member` refUsOccurredInF || ref `Set.member` refUsOccurredInB || pinnedRefU ref
          shouldKeep _ = True

          convert :: (GaloisField n, Integral n) => (RefB, Either (Bool, RefB) Bool) -> Maybe (Constraint n)
          convert (var, Right val) =
            if shouldKeep var
              then Just $ CVarBindB var (if val then 1 else 0)
              else Nothing
          convert (var, Left (True, root)) =
            if shouldKeep var || shouldKeep root
              then Just $ CVarEqB var root
              else Nothing
          convert (var, Left (False, root)) =
            if shouldKeep var || shouldKeep root
              then Just $ CVarNEqB var root
              else Nothing

          result = Maybe.mapMaybe convert $ Map.toList $ BooleanRelations.toIntMap relations
       in -- Seq.fromList
          --   (Maybe.mapMaybe toConstraint outputVars)
          --   <> Seq.fromList (Maybe.mapMaybe toConstraint publicInputVars)
          --   <> Seq.fromList (Maybe.mapMaybe toConstraint privateInputVars)
          --   <> Seq.fromList (Maybe.mapMaybe toConstraint occurredInF)
          --   <> Seq.fromList (Maybe.mapMaybe toConstraint occurredInB)
          --   <> Seq.fromList (Maybe.mapMaybe toConstraint occurredInU)
          -- <> Seq.fromList (Maybe.mapMaybe toConstraint (Set.toList occurredBitTests))
          Seq.fromList (map (fromConstraint counters) result)

    -- toConstraint var = case BooleanRelations.lookup relations var of
    --   BooleanRelations.Root ->
    --     -- var is already a root
    --     Nothing
    --   BooleanRelations.Constant intercept ->
    --     -- var = intercept
    --     Just $ fromConstraint counters $ CVarBindB var (if intercept then 1 else 0)
    --   BooleanRelations.ChildOf True root -> Just $ fromConstraint counters $ CVarEqB var root
    --   BooleanRelations.ChildOf False root -> Just $ fromConstraint counters $ CVarNEqB var root

    fromUIntRelations :: (GaloisField n, Integral n) => UIntRelations n -> Map RefF Int -> Map RefB Int -> Map RefU Int -> Seq (Relocated.Constraint n)
    fromUIntRelations uintRels _occurrencesF _occurrencesB _occurrencesU =
      let bitWidths = IntSet.toList $ IntMap.keysSet (structU (countOutput counters)) <> IntMap.keysSet (structU (countPublicInput counters)) <> IntMap.keysSet (structU (countPrivateInput counters)) <> IntMap.keysSet (structU (countIntermediate counters))
          outputVars = [RefUO w i | w <- bitWidths, i <- [0 .. getCount OfOutput (OfUInt w) counters - 1]]
          publicInputVars = [RefUI w i | w <- bitWidths, i <- [0 .. getCount OfPublicInput (OfUInt w) counters - 1]]
          privateInputVars = [RefUP w i | w <- bitWidths, i <- [0 .. getCount OfPrivateInput (OfUInt w) counters - 1]]
       in -- occurredInF = Map.keys $ Map.filterWithKey (\ref count -> count > 0 && not (pinnedRefF ref)) occurrencesF
          convert outputVars
            <> convert publicInputVars
            <> convert privateInputVars
      where
        -- <> convert binRepConstraints

        convert = Seq.fromList . Maybe.mapMaybe toConstraint

        -- generate a BinRep constraint for every UInt variable occurred in the module
        -- binRepConstraints = Map.keys $ Map.filterWithKey (\ref count -> count > 0 && not (pinnedRefU ref)) occurrencesU

        toConstraint var = case UIntRelations.lookup uintRels var of
          UIntRelations.Root -> Nothing
          UIntRelations.Constant value -> Just $ fromConstraint counters $ CVarBindU var value
          UIntRelations.ChildOf _ root ->
            -- case root of
            -- RefBtoRefU refB -> case BooleanRelations.lookup boolRels refB of
            --   BooleanRelations.Root -> case PolyG.build intercept [(var, -1), (root, slope)] of
            --     Left _ -> Nothing
            --     Right poly -> Just $ fromConstraint counters $ CAddF poly
            --   BooleanRelations.Constant intercept' ->
            --     -- root = intercept'
            --     Just $ fromConstraint counters $ CVarBindF var (slope * (if intercept' then 1 else 0) + intercept)
            --   BooleanRelations.ChildOf slope' root' ->
            --     -- root = slope' * root' + intercept'
            --     case PolyG.build intercept [(var, -1), (RefBtoRefF root', (if slope' then 1 else -1) * slope)] of
            --       Left _ -> Nothing
            --       Right poly -> Just $ fromConstraint counters $ CAddF poly
            case PolyG.build 0 [(RefUVal var, -1), (RefUVal root, 1)] of
              Left _ -> Nothing
              Right poly -> Just $ fromConstraint counters $ CAddF poly

    varEqFs = fromFieldRelations (csFieldRelations cs) (csUIntRelations cs) (csOccurrenceF cs) (csOccurrenceB cs) (csOccurrenceU cs)
    varEqUs = fromUIntRelations (csUIntRelations cs) (csOccurrenceF cs) (csOccurrenceB cs) (csOccurrenceU cs)
    -- traceShow (fromUIntRelations (csUIntRelations cs) (csOccurrenceF cs) (csOccurrenceB cs) (csOccurrenceU cs)) $
    -- traceShowId $ Seq.fromList $
    --   Maybe.mapMaybe (fromUIntRelationsOld (csOccurrenceU cs)) $
    --     Map.toList $
    --       UIntRelations.toMap $
    --         csUIntRelations cs
    addFs = Seq.fromList $ map (fromConstraint counters . CAddF) $ csAddF cs
    mulFs = Seq.fromList $ map (fromConstraint counters . uncurry3 CMulF) $ csMulF cs
    nEqFs = Seq.fromList $ map (\((x, y), m) -> Relocated.CNEq (Constraint.CNEQ (Left (reindexRefF counters x)) (Left (reindexRefF counters y)) (reindexRefF counters m))) $ Map.toList $ csNEqF cs
    nEqUs = Seq.fromList $ map (\((x, y), m) -> Relocated.CNEq (Constraint.CNEQ (Left (reindexRefU counters x)) (Left (reindexRefU counters y)) (reindexRefU counters m))) $ Map.toList $ csNEqU cs

sizeOfConstraintSystem :: ConstraintSystem n -> Int
sizeOfConstraintSystem cs =
  FieldRelations.size (csFieldRelations cs)
    + BooleanRelations.size (FieldRelations.exportBooleanRelations (csFieldRelations cs))
    + UIntRelations.size (csUIntRelations cs)
    + length (csAddF cs)
    + length (csMulF cs)
    + length (csNEqF cs)
    + length (csNEqU cs)

class UpdateOccurrences ref where
  addOccurrences :: [ref] -> ConstraintSystem n -> ConstraintSystem n
  removeOccurrences :: [ref] -> ConstraintSystem n -> ConstraintSystem n

instance UpdateOccurrences RefF where
  addOccurrences =
    flip
      ( foldl
          ( \cs ref ->
              case ref of
                RefBtoRefF refB ->
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
                RefBtoRefF refB ->
                  cs
                    { csOccurrenceB = Map.adjust (\count -> pred count `max` 0) refB (csOccurrenceB cs)
                    }
                _ ->
                  cs
                    { csOccurrenceF = Map.adjust (\count -> pred count `max` 0) ref (csOccurrenceF cs)
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
              case ref of
                RefBtoRefU refB ->
                  cs
                    { csOccurrenceB = Map.insertWith (+) refB 1 (csOccurrenceB cs)
                    }
                _ ->
                  cs
                    { csOccurrenceU = Map.insertWith (+) ref 1 (csOccurrenceU cs)
                    }
          )
      )
  removeOccurrences =
    flip
      ( foldl
          ( \cs ref ->
              case ref of
                RefBtoRefU refB ->
                  cs
                    { csOccurrenceB = Map.adjust (\count -> pred count `max` 0) refB (csOccurrenceB cs)
                    }
                _ ->
                  cs
                    { csOccurrenceU = Map.adjust (\count -> pred count `max` 0) ref (csOccurrenceU cs)
                    }
          )
      )
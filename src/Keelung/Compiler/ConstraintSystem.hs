{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.ConstraintSystem
  ( ConstraintSystem (..),
    relocateConstraintSystem,
    sizeOfConstraintSystem,
    addRefFOccurrences,
    addRefBOccurrences,
    addRefUOccurrences,
    removeRefFOccurrences,
    removeRefBOccurrences,
    removeRefUOccurrences,
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
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind)
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Keelung.Compiler.Relocated qualified as Relocated
import Keelung.Compiler.Util (indent)
import Keelung.Constraint.R1CS qualified as Constraint
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
    -- for counting the occurences of variables in constraints (excluding the ones that are in UnionFind)
    csOccurrenceF :: !(Map RefF Int),
    csOccurrenceB :: !(Map RefB Int),
    csOccurrenceU :: !(Map RefU Int),
    -- when x == y (UnionFind)
    csVarEqF :: UnionFind RefF n,
    csVarEqB :: BooleanRelations,
    csVarEqU :: UnionFind RefU n,
    -- addative constraints
    csAddF :: [PolyG RefF n],
    csAddU :: [PolyG RefU n],
    -- multiplicative constraints
    csMulF :: [(PolyG RefF n, PolyG RefF n, Either n (PolyG RefF n))],
    csMulB :: [(PolyG RefB n, PolyG RefB n, Either n (PolyG RefB n))],
    csMulU :: [(PolyG RefU n, PolyG RefU n, Either n (PolyG RefU n))],
    -- constraints for computing equality
    csNEqF :: Map (RefF, RefF) RefF,
    csNEqU :: Map (RefU, RefU) RefU
  }
  deriving (Eq, Generic, NFData)

instance (GaloisField n, Integral n) => Show (ConstraintSystem n) where
  show cs =
    "ConstraintSystem {\n"
      -- <> showVarBindF
      -- <> showVarBindB
      -- <> showVarBindU
      <> showVarEqF
      <> showVarEqB
      <> showVarEqU
      <> showAddF
      <> showAddU
      <> showMulF
      <> showMulB
      <> showMulU
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

      showVarEqF = "  VarEqF:\n" <> indent (indent (show (csVarEqF cs)))
      showVarEqB = "  VarEqB:\n" <> indent (indent (show (csVarEqB cs)))
      showVarEqU = "  VarEqU:\n" <> indent (indent (show (csVarEqU cs)))

      -- showVarBindU = adapt "VarBindU" (Map.toList $ csVarBindU cs) $ \(var, val) -> show var <> " = " <> show val
      -- showVarBindF = adapt "VarBindF" (Map.toList $ csVarBindF cs) $ \(var, val) -> show var <> " = " <> show val
      -- showVarBindB = adapt "VarBindB" (Map.toList $ csVarBindB cs) $ \(var, val) -> show var <> " = " <> show val

      showAddF = adapt "AddF" (csAddF cs) show
      showAddU = adapt "AddU" (csAddU cs) show

      showMulF = adapt "MulF" (csMulF cs) showMul
      showMulB = adapt "MulB" (csMulB cs) showMul
      showMulU = adapt "MulU" (csMulU cs) showMul

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
          <> varEqBs
          <> varEqUs
          -- <> varBindBs
          -- <> varBindUs
          <> addFs
          -- <> addBs
          <> addUs
          <> mulFs
          <> mulBs
          <> mulUs
          <> nEqFs
          <> nEqUs
    }
  where
    counters = csCounters cs
    uncurry3 f (a, b, c) = f a b c

    shouldRemoveU occurrences var =
      csUseNewOptimizer cs && case var of
        RefBtoRefU refB -> shouldRemoveB refB
        RefUO _ _ -> False
        RefUI _ _ -> False
        RefUP _ _ -> False
        RefU _ _ -> case Map.lookup var occurrences of
          Nothing -> True
          Just 0 -> True
          Just _ -> False

    shouldRemoveB _ = False

    fromUnionFindF :: (GaloisField n, Integral n) => UnionFind RefF n -> BooleanRelations -> Map RefF Int -> Seq (Relocated.Constraint n)
    fromUnionFindF unionFind boolRels occurrencesF =
      let outputVars = [RefFO i | i <- [0 .. getCount OfOutput OfField counters - 1]]
          publicInputVars = [RefFI i | i <- [0 .. getCount OfPublicInput OfField counters - 1]]
          privateInputVars = [RefFP i | i <- [0 .. getCount OfPrivateInput OfField counters - 1]]
          occurredInF = Map.keys $ Map.filterWithKey (\ref count -> count > 0 && not (pinnedRefF ref)) occurrencesF
       in Seq.fromList
            (Maybe.mapMaybe toConstraint outputVars)
            <> Seq.fromList (Maybe.mapMaybe toConstraint publicInputVars)
            <> Seq.fromList (Maybe.mapMaybe toConstraint privateInputVars)
            <> Seq.fromList (Maybe.mapMaybe toConstraint occurredInF)
      where
        -- <> Seq.fromList (Maybe.mapMaybe toConstraintRefB pairs)

        toConstraint var = case UnionFind.parentOf unionFind var of
          Nothing ->
            -- var is already a root
            Nothing
          Just (Nothing, intercept) ->
            -- var = intercept
            Just $ fromConstraint counters $ CVarBindF var intercept
          Just (Just (slope, root), intercept) ->
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

    fromUnionFindB :: (GaloisField n, Integral n) => BooleanRelations -> Map RefF Int -> Map RefB Int -> Map RefU Int -> Seq (Relocated.Constraint n)
    fromUnionFindB relations occurrencesF occurrencesB occurrencesU =
      let outputVars = [RefBO i | i <- [0 .. getCount OfOutput OfBoolean counters - 1]]
          publicInputVars = [RefBI i | i <- [0 .. getCount OfPublicInput OfBoolean counters - 1]]
          privateInputVars = [RefBP i | i <- [0 .. getCount OfPrivateInput OfBoolean counters - 1]]
          occurredInB = Map.keys $ Map.filter (> 0) occurrencesB

          findRefBInRefF (RefBtoRefF _) 0 = Nothing
          findRefBInRefF (RefBtoRefF r) _ = Just r
          findRefBInRefF _ _ = Nothing

          findRefBInRefU (RefBtoRefU _) 0 = Nothing
          findRefBInRefU (RefBtoRefU r) _ = Just r
          findRefBInRefU _ _ = Nothing

          occurredInF = Map.elems $ Map.mapMaybeWithKey findRefBInRefF occurrencesF
          occurredInU = Map.elems $ Map.mapMaybeWithKey findRefBInRefU occurrencesU
       in Seq.fromList
            (Maybe.mapMaybe toConstraint outputVars)
            <> Seq.fromList (Maybe.mapMaybe toConstraint publicInputVars)
            <> Seq.fromList (Maybe.mapMaybe toConstraint privateInputVars)
            <> Seq.fromList (Maybe.mapMaybe toConstraint occurredInF)
            <> Seq.fromList (Maybe.mapMaybe toConstraint occurredInB)
            <> Seq.fromList (Maybe.mapMaybe toConstraint occurredInU)
            <> Seq.fromList (Maybe.mapMaybe toConstraint (Set.toList (BooleanRelations.exportPinnedBitTests relations)))
      where
        toConstraint var = case BooleanRelations.lookup relations var of
          BooleanRelations.Root ->
            -- var is already a root
            Nothing
          BooleanRelations.Constant intercept ->
            -- var = intercept
            Just $ fromConstraint counters $ CVarBindB var (if intercept then 1 else 0)
          BooleanRelations.ChildOf True root -> Just $ fromConstraint counters $ CVarEqB var root
          BooleanRelations.ChildOf False root -> Just $ fromConstraint counters $ CVarNEqB var root
            -- -- var = slope * root + intercept
            -- case PolyG.build 0 [(var, -1), (root, if slope then 1 else -1)] of
            --   Left _ -> Nothing
            --   Right poly -> Just $ fromConstraint counters $ CAddB poly

    fromUnionFindU :: (GaloisField n, Integral n) => Map RefU Int -> (RefU, (Maybe (n, RefU), n)) -> Maybe (Relocated.Constraint n)
    fromUnionFindU occurrences (var1, (Nothing, c)) =
      if shouldRemoveU occurrences var1
        then Nothing
        else Just $ fromConstraint counters (CVarBindU var1 c)
    fromUnionFindU occurrences (var1, (Just (1, var2), 0)) =
      if shouldRemoveU occurrences var1 || shouldRemoveU occurrences var2
        then Nothing
        else Just $ fromConstraint counters (CVarEqU var1 var2)
    fromUnionFindU occurrences (var1, (Just (slope2, var2), intercept2)) =
      case PolyG.build intercept2 [(var1, -1), (var2, slope2)] of
        Left _ -> Nothing
        Right poly ->
          if shouldRemoveU occurrences var1 || shouldRemoveU occurrences var2
            then Nothing
            else Just $ fromConstraint counters (CAddU poly)

    varEqFs = fromUnionFindF (csVarEqF cs) (csVarEqB cs) (csOccurrenceF cs)
    -- varEqBs = Seq.fromList $ map (fromConstraint counters . uncurry CVarEqB) $ csVarEqB cs
    varEqBs = fromUnionFindB (csVarEqB cs) (csOccurrenceF cs) (csOccurrenceB cs) (csOccurrenceU cs)
    varEqUs = Seq.fromList $ Maybe.mapMaybe (fromUnionFindU (csOccurrenceU cs)) $ Map.toList $ UnionFind.toMap $ csVarEqU cs
    -- varEqUs = Seq.fromList $ map (fromConstraint counters . uncurry CVarEqU) $ csVarEqU cs
    -- varBindBs = Seq.fromList $ map (fromConstraint counters . uncurry CVarBindB) $ Map.toList $ csVarBindB cs
    -- varBindUs = Seq.fromList $ map (fromConstraint counters . uncurry CVarBindU) $ Map.toList $ csVarBindU cs
    addFs = Seq.fromList $ map (fromConstraint counters . CAddF) $ csAddF cs
    -- addBs = Seq.fromList $ map (fromConstraint counters . CAddB) $ csAddB cs
    addUs = Seq.fromList $ map (fromConstraint counters . CAddU) $ csAddU cs
    mulFs = Seq.fromList $ map (fromConstraint counters . uncurry3 CMulF) $ csMulF cs
    mulBs = Seq.fromList $ map (fromConstraint counters . uncurry3 CMulB) $ csMulB cs
    mulUs = Seq.fromList $ map (fromConstraint counters . uncurry3 CMulU) $ csMulU cs
    nEqFs = Seq.fromList $ map (\((x, y), m) -> Relocated.CNEq (Constraint.CNEQ (Left (reindexRefF counters x)) (Left (reindexRefF counters y)) (reindexRefF counters m))) $ Map.toList $ csNEqF cs
    nEqUs = Seq.fromList $ map (\((x, y), m) -> Relocated.CNEq (Constraint.CNEQ (Left (reindexRefU counters x)) (Left (reindexRefU counters y)) (reindexRefU counters m))) $ Map.toList $ csNEqU cs

sizeOfConstraintSystem :: ConstraintSystem n -> Int
sizeOfConstraintSystem cs =
  UnionFind.size (csVarEqF cs)
    + BooleanRelations.size (csVarEqB cs)
    + UnionFind.size (csVarEqU cs)
    -- + length (csVarBindF cs)
    -- + length (csVarBindB cs)
    -- + length (csVarBindU cs)
    + length (csAddF cs)
    + length (csAddU cs)
    + length (csMulF cs)
    + length (csMulB cs)
    + length (csMulU cs)
    + length (csNEqF cs)
    + length (csNEqU cs)

addRefFOccurrences :: [RefF] -> ConstraintSystem n -> ConstraintSystem n
addRefFOccurrences =
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

addRefBOccurrences :: [RefB] -> ConstraintSystem n -> ConstraintSystem n
addRefBOccurrences =
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

addRefUOccurrences :: [RefU] -> ConstraintSystem n -> ConstraintSystem n
addRefUOccurrences =
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

removeRefFOccurrences :: [RefF] -> ConstraintSystem n -> ConstraintSystem n
removeRefFOccurrences =
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

removeRefBOccurrences :: [RefB] -> ConstraintSystem n -> ConstraintSystem n
removeRefBOccurrences =
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

removeRefUOccurrences :: [RefU] -> ConstraintSystem n -> ConstraintSystem n
removeRefUOccurrences =
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
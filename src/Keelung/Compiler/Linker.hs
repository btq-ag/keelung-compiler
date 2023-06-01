{-# LANGUAGE BangPatterns #-}

module Keelung.Compiler.Linker (linkConstraintModule, reindexRef, Occurrences, constructOccurrences) where

import Control.Arrow (left)
import Data.Bifunctor (Bifunctor (bimap), first)
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
import Keelung.Compiler.Compile.IndexTable (IndexTable)
import Keelung.Compiler.Compile.IndexTable qualified as IndexTable
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.ConstraintSystem (ConstraintSystem (..))
import Keelung.Compiler.ConstraintSystem qualified as Linked
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
import Keelung.Compiler.Syntax.FieldBits qualified as FieldBits
import Keelung.Data.BinRep
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.Struct (Struct (..))
import Keelung.Syntax (HasWidth (widthOf), Var)
import Keelung.Syntax.Counters

-------------------------------------------------------------------------------

linkConstraintModule :: (GaloisField n, Integral n) => ConstraintModule n -> ConstraintSystem n
linkConstraintModule cm =
  ConstraintSystem
    { csField = cmField cm,
      csCounters = counters,
      csBinReps = binReps,
      csBinReps' = map (Seq.fromList . map (first (reindexRefB occurrences))) (cmBinReps cm),
      csConstraints =
        varEqFs
          <> varEqBs
          <> varEqUs
          <> addFs
          <> mulFs,
      csEqZeros = toList eqZeros,
      csDivMods = divMods,
      csModInvs = modInvs
    }
  where
    !occurrences = constructOccurrences (cmCounters cm) (cmOccurrenceF cm) (cmOccurrenceB cm) (cmOccurrenceU cm)
    !counters = updateCounters occurrences (cmCounters cm)
    uncurry3 f (a, b, c) = f a b c

    binReps = generateBinReps counters (cmOccurrenceU cm)

    -- \| Generate BinReps from the UIntRelations
    generateBinReps :: Counters -> OccurU -> [BinRep]
    generateBinReps (Counters o i1 i2 _ _ _ _) occurrencesU =
      toList $
        fromSmallCounter RefUO o
          <> fromSmallCounter RefUI i1
          <> fromSmallCounter RefUP i2
          <> intermediateBinReps
      where
        intermediateBinReps =
          Seq.fromList $
            concatMap
              ( \(width, xs) ->
                  mapMaybe
                    ( \(var, count) ->
                        let varOffset = reindexRef occurrences (U (RefUX width var))
                            binRepOffset = reindexRef occurrences (B (RefUBit width (RefUX width var) 0))
                         in if count > 0
                              then Just (BinRep varOffset width binRepOffset)
                              else Nothing
                    )
                    (IntMap.toList xs)
              )
              (OccurU.toList occurrencesU)

        -- fromSmallCounter :: VarSort -> SmallCounters -> [BinRep]
        fromSmallCounter refType (Struct _ _ u) = Seq.fromList $ concatMap (fromPair refType) (IntMap.toList u)

        -- fromPair :: VarSort -> (Width, Int) -> [BinRep]
        fromPair refType (width, count) =
          let varOffset = reindexRef occurrences (U (refType width 0))
              binRepOffset = reindexRef occurrences (B (RefUBit width (refType width 0) 0))
           in [BinRep (varOffset + index) width (binRepOffset + width * index) | index <- [0 .. count - 1]]

    extractFieldRelations :: (GaloisField n, Integral n) => AllRelations n -> Seq (Linked.Constraint n)
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
       in Seq.fromList (map (linkConstraint occurrences) result)

    shouldBeKept :: Ref -> Bool
    shouldBeKept (F ref) = refFShouldBeKept ref
    shouldBeKept (B ref) = refBShouldBeKept ref
    shouldBeKept (U ref) = refUShouldBeKept ref

    refFShouldBeKept :: RefF -> Bool
    refFShouldBeKept ref = case ref of
      RefFX var ->
        -- it's a Field intermediate variable that occurs in the circuit
        var `IntSet.member` refFsInOccurrencesF occurrences
      _ ->
        -- it's a pinned Field variable
        True

    refUShouldBeKept :: RefU -> Bool
    refUShouldBeKept ref = case ref of
      RefUX width var ->
        -- it's a UInt intermediate variable that occurs in the circuit
        ( case IntMap.lookup width (refUsInOccurrencesU occurrences) of
            Nothing -> False
            Just xs -> IntSet.member var xs
        )
      --   || ( case IntMap.lookup width (cmBitTests cm) of
      --          Nothing -> False
      --          Just xs -> IntSet.member var xs
      --      )
      _ ->
        -- it's a pinned UInt variable
        True

    refBShouldBeKept :: RefB -> Bool
    refBShouldBeKept ref = case ref of
      RefBX var ->
        --  it's a Boolean intermediate variable that occurs in the circuit
        var `IntSet.member` refBsInOccurrencesB occurrences
      -- \|| RefBX var `Set.member` refBsInOccurrencesF occurrences
      RefUBit _ var _ ->
        --  it's a Bit test of a UInt intermediate variable that occurs in the circuit
        --  the UInt variable should be kept
        shouldBeKept (U var)
      _ ->
        -- it's a pinned Field variable
        True

    extractBooleanRelations :: (GaloisField n, Integral n) => BooleanRelations -> Seq (Linked.Constraint n)
    extractBooleanRelations relations =
      let convert :: (GaloisField n, Integral n) => (RefB, Either (Bool, RefB) Bool) -> Constraint n
          convert (var, Right val) = CVarBindB var val
          convert (var, Left (dontFlip, root)) =
            if dontFlip
              then CVarEqB var root
              else CVarNEqB var root

          result = map convert $ Map.toList $ BooleanRelations.toMap refBShouldBeKept relations
       in Seq.fromList (map (linkConstraint occurrences) result)

    extractUIntRelations :: (GaloisField n, Integral n) => UIntRelations n -> Seq (Linked.Constraint n)
    extractUIntRelations relations =
      let convert :: (GaloisField n, Integral n) => (RefU, Either (Int, RefU) n) -> [Constraint n]
          convert (var, Right val) =
            let width = widthOf var
             in map (\i -> CVarBindB (RefUBit width var i) (FieldBits.testBit' val i)) [0 .. width - 1]
          convert (var, Left (rotation, root)) =
            let width = widthOf var
             in if rotation == 0
                  then map (\i -> CVarEqB (RefUBit width var i) (RefUBit width root i)) [0 .. width - 1]
                  else error "[ panic ] Unexpected rotation in extractUIntRelations"
          result = concatMap convert $ Map.toList $ UIntRelations.toMap refUShouldBeKept relations
       in Seq.fromList (map (linkConstraint occurrences) result)

    -- varEqFs = fromFieldRelations (cmFieldRelations cm) (FieldRelations.exportUIntRelations (cmFieldRelations cm)) (cmOccurrenceF cm)
    varEqFs = extractFieldRelations (cmFieldRelations cm)
    varEqUs = extractUIntRelations (FieldRelations.exportUIntRelations (cmFieldRelations cm))
    varEqBs = extractBooleanRelations (FieldRelations.exportBooleanRelations (cmFieldRelations cm))

    addFs = Seq.fromList $ map (linkConstraint occurrences . CAddF) $ cmAddF cm
    mulFs = Seq.fromList $ map (linkConstraint occurrences . uncurry3 CMulF) $ cmMulF cm
    eqZeros = Seq.fromList $ map (bimap (linkPoly_ occurrences) (reindexRefF occurrences)) $ cmEqZeros cm

    reindexBits refU =
      let width = widthOf refU
       in (reindexRefB occurrences (RefUBit (widthOf refU) refU 0), width)

    divMods = map (\(a, b, q, r) -> (left reindexBits a, left reindexBits b, left reindexBits q, left reindexBits r)) $ cmDivMods cm
    modInvs = map (\(a, output, n, p) -> (left reindexBits a, left reindexBits output, left reindexBits n, p)) $ cmModInvs cm

-------------------------------------------------------------------------------

linkConstraint :: (GaloisField n, Integral n) => Occurrences -> Constraint n -> Linked.Constraint n
linkConstraint counters (CAddF as) = Linked.CAdd (linkPoly_ counters as)
linkConstraint occurrences (CVarEq x y) =
  case Poly.buildEither 0 [(reindexRef occurrences x, 1), (reindexRef occurrences y, -1)] of
    Left _ -> error "CVarEq: two variables are the same"
    Right xs -> Linked.CAdd xs
linkConstraint counters (CVarEqF x y) =
  case Poly.buildEither 0 [(reindexRefF counters x, 1), (reindexRefF counters y, -1)] of
    Left _ -> error "CVarEqF: two variables are the same"
    Right xs -> Linked.CAdd xs
linkConstraint counters (CVarEqB x y) =
  case Poly.buildEither 0 [(reindexRefB counters x, 1), (reindexRefB counters y, -1)] of
    Left _ -> error $ "CVarEqB: two variables are the same" ++ show x ++ " " ++ show y
    Right xs -> Linked.CAdd xs
linkConstraint counters (CVarNEqB x y) =
  case Poly.buildEither 1 [(reindexRefB counters x, -1), (reindexRefB counters y, -1)] of
    Left _ -> error "CVarNEqB: two variables are the same"
    Right xs -> Linked.CAdd xs
linkConstraint counters (CVarBindF x n) = Linked.CAdd (Poly.bind (reindexRef counters x) n)
linkConstraint counters (CVarBindB x True) = Linked.CAdd (Poly.bind (reindexRefB counters x) 1)
linkConstraint counters (CVarBindB x False) = Linked.CAdd (Poly.bind (reindexRefB counters x) 0)
linkConstraint counters (CMulF as bs cs) =
  Linked.CMul
    (linkPoly_ counters as)
    (linkPoly_ counters bs)
    ( case cs of
        Left n -> Left n
        Right xs -> linkPoly counters xs
    )

updateCounters :: Occurrences -> Counters -> Counters
updateCounters occurrences counters =
  let reducedFX = (WriteField, getCount counters (Intermediate, ReadField) - IntSet.size (refFsInOccurrencesF occurrences))
      reducedBX = (WriteBool, getCount counters (Intermediate, ReadBool) - IntSet.size (refBsInOccurrencesB occurrences))
      reducedUXs = IntMap.mapWithKey (\width set -> (WriteUInt width, getCount counters (Intermediate, ReadUInt width) - IntSet.size set)) (refUsInOccurrencesU occurrences)
   in foldr (\(selector, reducedAmount) -> addCount (Intermediate, selector) (-reducedAmount)) counters $ reducedFX : reducedBX : IntMap.elems reducedUXs

--------------------------------------------------------------------------------

linkPoly :: (Integral n, GaloisField n) => Occurrences -> PolyG Ref n -> Either n (Poly n)
linkPoly occurrences poly = case PolyG.view poly of
  PolyG.Monomial constant (var, coeff) -> Poly.buildEither constant [(reindexRef occurrences var, coeff)]
  PolyG.Binomial constant (var1, coeff1) (var2, coeff2) -> Poly.buildEither constant [(reindexRef occurrences var1, coeff1), (reindexRef occurrences var2, coeff2)]
  PolyG.Polynomial constant xs -> Poly.buildEither constant (map (first (reindexRef occurrences)) (Map.toList xs))

linkPoly_ :: (Integral n, GaloisField n) => Occurrences -> PolyG Ref n -> Poly n
linkPoly_ occurrences xs = case linkPoly occurrences xs of
  Left _ -> error "[ panic ] linkPoly_: Left"
  Right p -> p

--------------------------------------------------------------------------------

reindexRef :: Occurrences -> Ref -> Var
reindexRef occurrences (F x) = reindexRefF occurrences x
reindexRef occurrences (B x) = reindexRefB occurrences x
reindexRef occurrences (U x) = reindexRefU occurrences x

reindexRefF :: Occurrences -> RefF -> Var
reindexRefF occurrences (RefFO x) = reindex (occurCounters occurrences) Output ReadField x
reindexRefF occurrences (RefFI x) = reindex (occurCounters occurrences) PublicInput ReadField x
reindexRefF occurrences (RefFP x) = reindex (occurCounters occurrences) PrivateInput ReadField x
reindexRefF occurrences (RefFX x) = IndexTable.reindex (indexTable occurrences) (reindex (occurCounters occurrences) Intermediate ReadField x - pinnedSize occurrences) + pinnedSize occurrences

reindexRefB :: Occurrences -> RefB -> Var
reindexRefB occurrences (RefBO x) = reindex (occurCounters occurrences) Output ReadBool x
reindexRefB occurrences (RefBI x) = reindex (occurCounters occurrences) PublicInput ReadBool x
reindexRefB occurrences (RefBP x) = reindex (occurCounters occurrences) PrivateInput ReadBool x
reindexRefB occurrences (RefBX x) = IndexTable.reindex (indexTable occurrences) (reindex (occurCounters occurrences) Intermediate ReadBool x - pinnedSize occurrences) + pinnedSize occurrences
reindexRefB occurrences (RefUBit _ x i) =
  case x of
    RefUO w x' -> reindex (occurCounters occurrences) Output (ReadBits w) x' + (i `mod` w)
    RefUI w x' -> reindex (occurCounters occurrences) PublicInput (ReadBits w) x' + (i `mod` w)
    RefUP w x' -> reindex (occurCounters occurrences) PrivateInput (ReadBits w) x' + (i `mod` w)
    RefUX w x' -> IndexTable.reindex (indexTable occurrences) (reindex (occurCounters occurrences) Intermediate (ReadBits w) x' - pinnedSize occurrences) + pinnedSize occurrences + (i `mod` w)

reindexRefU :: Occurrences -> RefU -> Var
reindexRefU occurrences (RefUO w x) = reindex (occurCounters occurrences) Output (ReadUInt w) x
reindexRefU occurrences (RefUI w x) = reindex (occurCounters occurrences) PublicInput (ReadUInt w) x
reindexRefU occurrences (RefUP w x) = reindex (occurCounters occurrences) PrivateInput (ReadUInt w) x
reindexRefU occurrences (RefUX w x) = IndexTable.reindex (indexTable occurrences) (reindex (occurCounters occurrences) Intermediate (ReadUInt w) x - pinnedSize occurrences) + pinnedSize occurrences

-------------------------------------------------------------------------------

-- | Allow us to determine which relations should be extracted from the pool
data Occurrences = Occurrences
  { occurCounters :: !Counters,
    refFsInOccurrencesF :: !IntSet,
    refBsInOccurrencesB :: !IntSet,
    refUsInOccurrencesU :: !(IntMap IntSet),
    indexTable :: !IndexTable,
    pinnedSize :: !Int
  }

-- | Smart constructor for 'Occurrences'
constructOccurrences :: Counters -> OccurF -> OccurB -> OccurU -> Occurrences
constructOccurrences counters occurF occurB occurU =
  Occurrences
    { occurCounters = counters,
      refFsInOccurrencesF = OccurF.occuredSet occurF,
      refBsInOccurrencesB = OccurB.occuredSet occurB,
      refUsInOccurrencesU = OccurU.occuredSet occurU,
      indexTable =
        OccurF.toIndexTable counters occurF
          <> OccurB.toIndexTable counters occurB
          <> OccurU.toIndexTable counters occurU,
      pinnedSize = getCount counters Output + getCount counters PublicInput + getCount counters PrivateInput
    }
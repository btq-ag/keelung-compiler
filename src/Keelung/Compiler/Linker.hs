{-# LANGUAGE TupleSections #-}

module Keelung.Compiler.Linker (linkConstraintModule) where

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
import Data.Set qualified as Set
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.ConstraintSystem (ConstraintSystem (..))
import Keelung.Compiler.ConstraintSystem qualified as Linked
import Keelung.Compiler.Optimize.OccurB qualified as OccurB
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
import Keelung.Data.BinRep
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.Struct (Struct (..))
import Keelung.Syntax.Counters
import Keelung.Syntax (Var)

-------------------------------------------------------------------------------

linkConstraintModule :: (GaloisField n, Integral n) => ConstraintModule n -> ConstraintSystem n
linkConstraintModule cm =
  ConstraintSystem
    { csField = cmField cm,
      csCounters = counters,
      csBinReps = binReps,
      csBinReps' = map (Seq.fromList . map (first (reindexRefB counters))) (cmBinReps cm),
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
       in Seq.fromList (map (linkConstraint counters) result)

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

    extractBooleanRelations :: (GaloisField n, Integral n) => BooleanRelations -> Seq (Linked.Constraint n)
    extractBooleanRelations relations =
      let convert :: (GaloisField n, Integral n) => (RefB, Either (Bool, RefB) Bool) -> Constraint n
          convert (var, Right val) = CVarBindB var val
          convert (var, Left (dontFlip, root)) =
            if dontFlip
              then CVarEqB var root
              else CVarNEqB var root

          result = map convert $ Map.toList $ BooleanRelations.toMap refBShouldBeKept relations
       in Seq.fromList (map (linkConstraint counters) result)

    extractUIntRelations :: (GaloisField n, Integral n) => UIntRelations n -> Seq (Linked.Constraint n)
    extractUIntRelations relations =
      let convert :: (GaloisField n, Integral n) => (RefU, Either (Int, RefU) n) -> Constraint n
          convert (var, Right val) = CVarBindU var val
          convert (var, Left (rotation, root)) =
            if rotation == 0
              then CVarEqU var root
              else error "[ panic ] Unexpected rotation in extractUIntRelations"

          result = map convert $ Map.toList $ UIntRelations.toMap refUShouldBeKept relations
       in Seq.fromList (map (linkConstraint counters) result)

    -- varEqFs = fromFieldRelations (cmFieldRelations cm) (FieldRelations.exportUIntRelations (cmFieldRelations cm)) (cmOccurrenceF cm)
    varEqFs = extractFieldRelations (cmFieldRelations cm)
    varEqUs = extractUIntRelations (FieldRelations.exportUIntRelations (cmFieldRelations cm))
    varEqBs = extractBooleanRelations (FieldRelations.exportBooleanRelations (cmFieldRelations cm))

    addFs = Seq.fromList $ map (linkConstraint counters . CAddF) $ cmAddF cm
    mulFs = Seq.fromList $ map (linkConstraint counters . uncurry3 CMulF) $ cmMulF cm
    eqZeros = Seq.fromList $ map (bimap (linkPoly_ counters) (reindexRefF counters)) $ cmEqZeros cm

    divMods = map (\(a, b, q, r) -> (left (reindexRefU counters) a, left (reindexRefU counters) b, left (reindexRefU counters) q, left (reindexRefU counters) r)) $ cmDivMods cm
    modInvs = map (\(a, n, p) -> (left (reindexRefU counters) a, left (reindexRefU counters) n, p)) $ cmModInvs cm

-------------------------------------------------------------------------------

linkConstraint :: (GaloisField n, Integral n) => Counters -> Constraint n -> Linked.Constraint n
linkConstraint counters (CAddF as) = Linked.CAdd (linkPoly_ counters as)
linkConstraint counters (CVarEq x y) =
  case Poly.buildEither 0 [(reindexRef counters x, 1), (reindexRef counters y, -1)] of
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
linkConstraint counters (CVarEqU x y) =
  case Poly.buildEither 0 [(reindexRefU counters x, 1), (reindexRefU counters y, -1)] of
    Left _ -> error "CVarEqU: two variables are the same"
    Right xs -> Linked.CAdd xs
linkConstraint counters (CVarBindF x n) = Linked.CAdd (Poly.bind (reindexRef counters x) n)
linkConstraint counters (CVarBindB x True) = Linked.CAdd (Poly.bind (reindexRefB counters x) 1)
linkConstraint counters (CVarBindB x False) = Linked.CAdd (Poly.bind (reindexRefB counters x) 0)
linkConstraint counters (CVarBindU x n) = Linked.CAdd (Poly.bind (reindexRefU counters x) n)
linkConstraint counters (CMulF as bs cs) =
  Linked.CMul
    (linkPoly_ counters as)
    (linkPoly_ counters bs)
    ( case cs of
        Left n -> Left n
        Right xs -> linkPoly counters xs
    )

--------------------------------------------------------------------------------

linkPoly :: (Integral n, GaloisField n) => Counters -> PolyG Ref n -> Either n (Poly n)
linkPoly counters poly = case PolyG.view poly of
  PolyG.Monomial constant (var, coeff) -> Poly.buildEither constant [(reindexRef counters var, coeff)]
  PolyG.Binomial constant (var1, coeff1) (var2, coeff2) -> Poly.buildEither constant [(reindexRef counters var1, coeff1), (reindexRef counters var2, coeff2)]
  PolyG.Polynomial constant xs -> Poly.buildEither constant (map (first (reindexRef counters)) (Map.toList xs))

linkPoly_ :: (Integral n, GaloisField n) => Counters -> PolyG Ref n -> Poly n
linkPoly_ counters xs = case linkPoly counters xs of
  Left _ -> error "[ panic ] linkPoly_: Left"
  Right p -> p

--------------------------------------------------------------------------------

reindexRef :: Counters -> Ref -> Var
reindexRef counters (F x) = reindexRefF counters x
reindexRef counters (B x) = reindexRefB counters x
reindexRef counters (U x) = reindexRefU counters x

reindexRefF :: Counters -> RefF -> Var
reindexRefF counters (RefFO x) = reindex counters Output ReadField x
reindexRefF counters (RefFI x) = reindex counters PublicInput ReadField x
reindexRefF counters (RefFP x) = reindex counters PrivateInput ReadField x
reindexRefF counters (RefFX x) = reindex counters Intermediate ReadField x

reindexRefB :: Counters -> RefB -> Var
reindexRefB counters (RefBO x) = reindex counters Output ReadBool x
reindexRefB counters (RefBI x) = reindex counters PublicInput ReadBool x
reindexRefB counters (RefBP x) = reindex counters PrivateInput ReadBool x
reindexRefB counters (RefBX x) = reindex counters Intermediate ReadBool x
reindexRefB counters (RefUBit _ x i) =
  case x of
    RefUO w x' -> reindex counters Output (ReadBits w) x' + (i `mod` w)
    RefUI w x' -> reindex counters PublicInput (ReadBits w) x' + (i `mod` w)
    RefUP w x' -> reindex counters PrivateInput (ReadBits w) x' + (i `mod` w)
    RefUX w x' -> reindex counters Intermediate (ReadBits w) x' + (i `mod` w)

reindexRefU :: Counters -> RefU -> Var
reindexRefU counters (RefUO w x) = reindex counters Output (ReadUInt w) x
reindexRefU counters (RefUI w x) = reindex counters PublicInput (ReadUInt w) x
reindexRefU counters (RefUP w x) = reindex counters PrivateInput (ReadUInt w) x
reindexRefU counters (RefUX w x) = reindex counters Intermediate (ReadUInt w) x

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
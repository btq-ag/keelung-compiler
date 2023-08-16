{-# LANGUAGE BangPatterns #-}

module Keelung.Compiler.Linker (linkConstraintModule, reindexRef, Occurrences, constructOccurrences) where

import Data.Bifunctor (Bifunctor (bimap, first))
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Keelung.Compiler.Compile.IndexTable (IndexTable)
import Keelung.Compiler.Compile.IndexTable qualified as IndexTable
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
import Keelung.Compiler.Relations.Field (Relations)
import Keelung.Compiler.Relations.Field qualified as Relations
import Keelung.Compiler.Relations.Field qualified as FieldRelations
import Keelung.Data.Constraint
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Data.PolyL
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.Reference
import Keelung.Interpreter.Arithmetics (U)
import Keelung.Interpreter.Arithmetics qualified as U
import Keelung.Syntax (HasWidth (widthOf), Var, Width)
import Keelung.Syntax.Counters

-------------------------------------------------------------------------------

linkConstraintModule :: (GaloisField n, Integral n) => ConstraintModule n -> ConstraintSystem n
linkConstraintModule cm =
  ConstraintSystem
    { csField = cmField cm,
      csCounters = counters,
      csConstraints =
        varEqFs
          <> varEqBs
          <> addFs
          <> addLs
          <> mulFs
          <> mulLs,
      csEqZeros = toList eqZeros,
      csDivMods = divMods,
      csModInvs = modInvs
    }
  where
    !occurrences = constructOccurrences (cmCounters cm) (cmOccurrenceF cm) (cmOccurrenceB cm) (cmOccurrenceU cm)
    !counters = updateCounters occurrences (cmCounters cm)
    uncurry3 f (a, b, c) = f a b c

    extractFieldRelations :: (GaloisField n, Integral n) => Relations n -> Seq (Linked.Constraint n)
    extractFieldRelations relations =
      let convert :: (GaloisField n, Integral n) => (Ref, Either (n, Ref, n) n) -> Constraint n
          convert (var, Right val) = CVarBindF var val
          convert (var, Left (slope, root, intercept)) =
            case (slope, intercept) of
              (0, _) -> CVarBindF var intercept
              (1, 0) -> CVarEq var root
              (_, _) -> case PolyG.build intercept [(var, -1), (root, slope)] of
                Left _ -> error "[ panic ] extractFieldRelations: failed to build polynomial"
                Right poly -> CAddG poly

          result = map convert $ Map.toList $ Relations.toInt shouldBeKept relations
       in Seq.fromList (map (linkConstraint occurrences) result)

    shouldBeKept :: Ref -> Bool
    shouldBeKept (F ref) = refFShouldBeKept ref
    shouldBeKept (B ref) = refBShouldBeKept ref

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
        refUShouldBeKept var
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

    varEqFs = extractFieldRelations (cmRelations cm)
    varEqBs = extractBooleanRelations (FieldRelations.exportBooleanRelations (cmRelations cm))

    addFs = Seq.fromList $ map (linkConstraint occurrences . CAddG) $ cmAddF cm
    addLs = Seq.fromList $ map (linkConstraint occurrences . CAddL) $ cmAddL cm
    mulFs = Seq.fromList $ map (linkConstraint occurrences . uncurry3 CMulF) $ cmMulF cm
    mulLs = Seq.fromList $ map (linkConstraint occurrences . uncurry3 CMulL) $ cmMulL cm
    eqZeros = Seq.fromList $ map (bimap (linkPolyGUnsafe occurrences) (reindexRefF occurrences)) $ cmEqZeros cm

    fromEitherRefU :: Either RefU U -> (Width, Either Var Integer)
    fromEitherRefU (Left var) = let width = widthOf var in (width, Left (reindexRefB occurrences (RefUBit width var 0)))
    fromEitherRefU (Right val) = let width = U.uintWidth val in (width, Right (U.uintValue val))

    divMods = map (\(a, b, q, r) -> (fromEitherRefU a, fromEitherRefU b, fromEitherRefU q, fromEitherRefU r)) $ cmDivMods cm
    modInvs = map (\(a, output, n, p) -> (fromEitherRefU a, fromEitherRefU output, fromEitherRefU n, U.uintValue p)) $ cmModInvs cm

-------------------------------------------------------------------------------

linkConstraint :: (GaloisField n, Integral n) => Occurrences -> Constraint n -> Linked.Constraint n
linkConstraint counters (CAddG as) = Linked.CAdd (linkPolyGUnsafe counters as)
linkConstraint counters (CAddL as) = Linked.CAdd (linkPolyLUnsafe counters as)
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
linkConstraint counters (CVarBindF x n) = case Poly.buildEither (-n) [(reindexRef counters x, 1)] of
  Left _ -> error "CVarBindF: impossible"
  Right xs -> Linked.CAdd xs
linkConstraint counters (CVarBindB x True) = Linked.CAdd (Poly.bind (reindexRefB counters x) 1)
linkConstraint counters (CVarBindB x False) = Linked.CAdd (Poly.bind (reindexRefB counters x) 0)
linkConstraint counters (CMulF as bs cs) =
  Linked.CMul
    (linkPolyGUnsafe counters as)
    (linkPolyGUnsafe counters bs)
    ( case cs of
        Left n -> Left n
        Right xs -> linkPolyG counters xs
    )
linkConstraint counters (CMulL as bs cs) =
  Linked.CMul
    (linkPolyLUnsafe counters as)
    (linkPolyLUnsafe counters bs)
    ( case cs of
        Left n -> Left n
        Right xs -> linkPolyL counters xs
    )

updateCounters :: Occurrences -> Counters -> Counters
updateCounters occurrences counters =
  let reducedFX = (WriteField, getCount counters (Intermediate, ReadField) - IntSet.size (refFsInOccurrencesF occurrences))
      reducedBX = (WriteBool, getCount counters (Intermediate, ReadBool) - IntSet.size (refBsInOccurrencesB occurrences))
      reducedUXs = IntMap.mapWithKey (\width set -> (WriteUInt width, getCount counters (Intermediate, ReadUInt width) - IntSet.size set)) (refUsInOccurrencesU occurrences)
   in foldr (\(selector, reducedAmount) -> addCount (Intermediate, selector) (-reducedAmount)) counters $ reducedFX : reducedBX : IntMap.elems reducedUXs

--------------------------------------------------------------------------------

linkPolyG :: (Integral n, GaloisField n) => Occurrences -> PolyG n -> Either n (Poly n)
linkPolyG occurrences poly = case PolyG.view poly of
  PolyG.Monomial constant (var, coeff) -> Poly.buildEither constant [(reindexRef occurrences var, coeff)]
  PolyG.Binomial constant (var1, coeff1) (var2, coeff2) -> Poly.buildEither constant [(reindexRef occurrences var1, coeff1), (reindexRef occurrences var2, coeff2)]
  PolyG.Polynomial constant xs -> Poly.buildEither constant $ fmap (first (reindexRef occurrences)) (Map.toList xs)

linkPolyGUnsafe :: (Integral n, GaloisField n) => Occurrences -> PolyG n -> Poly n
linkPolyGUnsafe occurrences xs = case linkPolyG occurrences xs of
  Left _ -> error "[ panic ] linkPolyGUnsafe: Left"
  Right p -> p

linkPolyL :: (Integral n, GaloisField n) => Occurrences -> PolyL n -> Either n (Poly n)
linkPolyL occurrences (PolyL constant limbs) = Poly.buildEither constant $ toList $ mconcat (fmap (uncurry (reindexRefL occurrences)) (toList limbs))

linkPolyLUnsafe :: (Integral n, GaloisField n) => Occurrences -> PolyL n -> Poly n
linkPolyLUnsafe occurrences xs = case linkPolyL occurrences xs of
  Left _ -> error "[ panic ] linkPolyLUnsafe: Left"
  Right p -> p

--------------------------------------------------------------------------------

reindexRef :: Occurrences -> Ref -> Var
reindexRef occurrences (F x) = reindexRefF occurrences x
reindexRef occurrences (B x) = reindexRefB occurrences x

reindexRefL :: (Integral n, GaloisField n) => Occurrences -> RefL -> n -> Seq (Var, n)
reindexRefL occurrences (RefL limb powerOffset) multiplier = case lmbSigns limb of
  Left sign ->
    Seq.fromList
      [ ( reindexRefU
            occurrences
            (lmbRef limb)
            (i + lmbOffset limb),
          (2 ^ (i + powerOffset)) * if sign then multiplier else (-multiplier)
        )
        | i <- [0 .. lmbWidth limb - 1]
      ]
  Right signs ->
    Seq.fromList
      [ ( reindexRefU
            occurrences
            (lmbRef limb)
            (i + lmbOffset limb),
          (2 ^ (i + powerOffset)) * if sign then multiplier else (-multiplier)
        )
        | (i, sign) <- zip [0 .. lmbWidth limb - 1] signs
      ]

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
reindexRefB occurrences (RefUBit _ x i) = reindexRefU occurrences x i

reindexRefU :: Occurrences -> RefU -> Int -> Var
reindexRefU occurrences (RefUO w x) i = reindex (occurCounters occurrences) Output (ReadUInt w) x + (i `mod` w)
reindexRefU occurrences (RefUI w x) i = reindex (occurCounters occurrences) PublicInput (ReadUInt w) x + (i `mod` w)
reindexRefU occurrences (RefUP w x) i = reindex (occurCounters occurrences) PrivateInput (ReadUInt w) x + (i `mod` w)
reindexRefU occurrences (RefUX w x) i = IndexTable.reindex (indexTable occurrences) (reindex (occurCounters occurrences) Intermediate (ReadUInt w) x - pinnedSize occurrences) + pinnedSize occurrences + (i `mod` w)

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
  deriving (Show)

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
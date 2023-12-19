{-# LANGUAGE BangPatterns #-}

module Keelung.Compiler.Linker (linkConstraintModule, reindexRef, Occurrences, constructOccurrences) where

import Data.Bifunctor (Bifunctor (bimap, first))
import Data.Bits qualified
import Data.Foldable (toList)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Keelung
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.ConstraintSystem (ConstraintSystem (..))
import Keelung.Compiler.ConstraintSystem qualified as Linked
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
import Keelung.Compiler.Relations.Limb (LimbRelations)
import Keelung.Compiler.Relations.Limb qualified as LimbRelations
import Keelung.Compiler.Relations.UInt (UIntRelations)
import Keelung.Compiler.Relations.UInt qualified as UIntRelations
import Keelung.Data.Constraint
import Keelung.Data.FieldInfo (FieldInfo)
import Keelung.Data.FieldInfo qualified as FieldInfo
import Keelung.Data.IntervalTable (IntervalTable)
import Keelung.Data.IntervalTable qualified as IntervalTable
import Keelung.Data.Limb (Limb (..))
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.PolyL
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.Reference
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Syntax.Counters

-------------------------------------------------------------------------------

linkConstraintModule :: (GaloisField n, Integral n) => ConstraintModule n -> ConstraintSystem n
linkConstraintModule cm =
  ConstraintSystem
    { csField = cmField cm,
      csCounters = counters,
      csConstraints =
        varEqFs
          <> varEqLs
          <> varEqUs
          <> addLs
          <> mulLs,
      csEqZeros = toList eqZeros,
      csDivMods = map (\(a, b, c, d) -> ([a], [b], [c], [d])) divMods,
      csCLDivMods = map (\(a, b, c, d) -> ([a], [b], [c], [d])) clDivMods,
      csModInvs = map (\(a, b, c, d) -> ([a], [b], [c], d)) modInvs
    }
  where
    !occurrences = constructOccurrences (cmCounters cm) (cmOccurrenceF cm) (cmOccurrenceB cm) (cmOccurrenceU cm) (cmOccurrenceUB cm)
    !counters = updateCounters occurrences (cmCounters cm)
    uncurry3 f (a, b, c) = f a b c

    fieldWidth = FieldInfo.fieldWidth (cmField cm)

    extractRefRelations :: (GaloisField n, Integral n) => Relations n -> Seq (Linked.Constraint n)
    extractRefRelations relations =
      let convert :: (GaloisField n, Integral n) => (Ref, Either (n, Ref, n) n) -> Constraint n
          convert (var, Right val) = CRefFVal var val
          convert (var, Left (slope, root, intercept)) =
            case (slope, intercept) of
              (0, _) -> CRefFVal var intercept
              (1, 0) -> CRefEq var root
              (_, _) -> case PolyL.fromRefs intercept [(var, -1), (root, slope)] of
                Left _ -> error "[ panic ] extractRefRelations: failed to build polynomial"
                Right poly -> CAddL poly

          result = map convert $ Map.toList $ Relations.toInt shouldBeKept relations
       in Seq.fromList (linkConstraint (cmField cm) occurrences fieldWidth =<< result)

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

    limbShouldBeKept :: Limb -> Bool
    limbShouldBeKept limb =
      if useNewLinker
        then case lmbRef limb of
          RefUX width var -> case IntMap.lookup width (refBsInOccurrencesUB occurrences) of
            Nothing -> False
            Just table -> IntervalTable.member (width * var + lmbOffset limb, width * var + lmbOffset limb + lmbWidth limb) table
          _ -> True -- it's a pinned UInt variable
        else refUShouldBeKept (lmbRef limb)

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

    extractLimbRelations :: (GaloisField n, Integral n) => LimbRelations -> Seq (Linked.Constraint n)
    extractLimbRelations relations =
      let convert :: (GaloisField n, Integral n) => (Limb, Either Limb Integer) -> Constraint n
          convert (var, Right val) = CLimbVal var val
          convert (var, Left root) = CLimbEq var root

          result = map convert $ Map.toList $ LimbRelations.toMap limbShouldBeKept relations
       in Seq.fromList (linkConstraint (cmField cm) occurrences fieldWidth =<< result)

    extractUIntRelations :: (GaloisField n, Integral n) => UIntRelations -> Seq (Linked.Constraint n)
    extractUIntRelations relations = UIntRelations.toConstraints refUShouldBeKept relations >>= Seq.fromList . linkConstraint (cmField cm) occurrences fieldWidth

    varEqFs = extractRefRelations (cmRelations cm)
    varEqLs = extractLimbRelations (Relations.exportLimbRelations (cmRelations cm))
    varEqUs = extractUIntRelations (Relations.exportUIntRelations (cmRelations cm))

    addLs = Seq.fromList $ linkConstraint (cmField cm) occurrences fieldWidth . CAddL =<< cmAddL cm
    mulLs = Seq.fromList $ linkConstraint (cmField cm) occurrences fieldWidth . uncurry3 CMulL =<< cmMulL cm
    eqZeros = Seq.fromList $ map (bimap (linkPolyLUnsafe occurrences) (reindexRefF occurrences)) $ cmEqZeros cm

    fromEitherRefU :: Either RefU U -> (Width, Either Var Integer)
    fromEitherRefU (Left var) = let width = widthOf var in (width, Left (reindexRefB occurrences (RefUBit width var 0)))
    fromEitherRefU (Right val) = let width = widthOf val in (width, Right (U.uValue val))

    divMods = map (\(a, b, q, r) -> (fromEitherRefU a, fromEitherRefU b, fromEitherRefU q, fromEitherRefU r)) $ cmDivMods cm
    clDivMods = map (\(a, b, q, r) -> (fromEitherRefU a, fromEitherRefU b, fromEitherRefU q, fromEitherRefU r)) $ cmCLDivMods cm
    modInvs = map (\(a, output, n, p) -> (fromEitherRefU a, fromEitherRefU output, fromEitherRefU n, U.uValue p)) $ cmModInvs cm

-------------------------------------------------------------------------------

-- | Link a specialized constraint to a list of constraints
linkConstraint :: (GaloisField n, Integral n) => FieldInfo -> Occurrences -> Width -> Constraint n -> [Linked.Constraint n]
linkConstraint _ occurrences _ (CAddL as) = [Linked.CAdd (linkPolyLUnsafe occurrences as)]
linkConstraint _ occurrences _ (CRefEq x y) =
  case Poly.buildEither 0 [(reindexRef occurrences x, 1), (reindexRef occurrences y, -1)] of
    Left _ -> error "CRefEq: two references are the same"
    Right xs -> [Linked.CAdd xs]
linkConstraint _ occurrences _ (CRefBNEq x y) =
  case Poly.buildEither 1 [(reindexRefB occurrences x, -1), (reindexRefB occurrences y, -1)] of
    Left _ -> error "CRefBNEq: two variables are the same"
    Right xs -> [Linked.CAdd xs]
linkConstraint fieldInfo occurrences _ (CLimbEq x y) =
  if lmbWidth x /= lmbWidth y
    then error "[ panic ] CLimbEq: Limbs are of different width"
    else do
      case FieldInfo.fieldTypeData fieldInfo of
        Binary _ -> do
          i <- [0 .. lmbWidth x - 1]
          let pair = [(reindexRefU occurrences (lmbRef x) (lmbOffset x + i), 1), (reindexRefU occurrences (lmbRef y) (lmbOffset y + i), -1)]
          case Poly.buildEither 0 pair of
            Left _ -> error "CLimbEq: two variables are the same"
            Right xs -> [Linked.CAdd xs]
        Prime _ -> do
          let pairsX = reindexLimb occurrences x 1
          let pairsY = reindexLimb occurrences y (-1)
          let pairs = IntMap.unionWith (+) pairsX pairsY
          case Poly.buildWithIntMap 0 pairs of
            Left _ -> error "CLimbEq: two variables are the same"
            Right xs -> [Linked.CAdd xs]
linkConstraint fieldInfo occurrences fieldWidth (CRefUEq x y) =
  -- split `x` and `y` into smaller limbs and pair them up with `CLimbEq`
  let cVarEqLs = zipWith CLimbEq (Limb.refUToLimbs fieldWidth x) (Limb.refUToLimbs fieldWidth y)
   in cVarEqLs >>= linkConstraint fieldInfo occurrences fieldWidth
linkConstraint _ occurrences _ (CRefFVal x n) = case Poly.buildEither (-n) [(reindexRef occurrences x, 1)] of
  Left _ -> error "CRefFVal: impossible"
  Right xs -> [Linked.CAdd xs]
linkConstraint fieldInfo occurrences _ (CLimbVal x n) =
  -- "ArithException: arithmetic underflow" will be thrown if `n` is negative in Binary fields
  let negatedConstant = case FieldInfo.fieldTypeData fieldInfo of
        Prime _ -> fromInteger (-n)
        Binary _ -> fromInteger n
   in case Poly.buildWithIntMap negatedConstant (reindexLimb occurrences x 1) of
        Left _ -> error "CLimbVal: impossible"
        Right xs -> [Linked.CAdd xs]
linkConstraint fieldInfo occurrences fieldWidth (CRefUVal x n) =
  case FieldInfo.fieldTypeData fieldInfo of
    Binary _ ->
      let width = widthOf x
          cRefFVals = [CRefFVal (B (RefUBit width x i)) (if Data.Bits.testBit n i then 1 else 0) | i <- [0 .. widthOf x - 1]]
       in cRefFVals >>= linkConstraint fieldInfo occurrences fieldWidth
    Prime _ -> do
      -- split the Integer into smaller chunks of size `fieldWidth`
      let number = U.new (widthOf x) n
          chunks = map U.uValue (U.chunks fieldWidth number)
          cLimbVals = zipWith CLimbVal (Limb.refUToLimbs fieldWidth x) chunks
       in cLimbVals >>= linkConstraint fieldInfo occurrences fieldWidth
linkConstraint _ occurrences _ (CMulL as bs cs) =
  [ Linked.CMul
      (linkPolyLUnsafe occurrences as)
      (linkPolyLUnsafe occurrences bs)
      ( case cs of
          Left n -> Left n
          Right xs -> linkPolyL occurrences xs
      )
  ]

updateCounters :: Occurrences -> Counters -> Counters
updateCounters occurrences counters =
  let reducedFX = (WriteField, getCount counters (Intermediate, ReadField) - IntSet.size (refFsInOccurrencesF occurrences))
      reducedBX = (WriteBool, getCount counters (Intermediate, ReadBool) - IntSet.size (refBsInOccurrencesB occurrences))
      reducedUXs =
        if useNewLinker
          then
            IntMap.mapWithKey
              ( \width table ->
                  let original = getCount counters (Intermediate, ReadUInt width) -- thie is the number of UInt variables used before optimization & linking (regardless of width)
                      current = IntervalTable.size table -- this is the number of bits used after optimization & linking
                   in (WriteUInt width, original - current)
              )
              (refBsInOccurrencesUB occurrences)
          else IntMap.mapWithKey (\width set -> (WriteUInt width, getCount counters (Intermediate, ReadUInt width) - IntSet.size set)) (refUsInOccurrencesU occurrences)
   in foldr (\(selector, reducedAmount) -> addCount (Intermediate, selector) (-reducedAmount)) counters $ reducedFX : reducedBX : IntMap.elems reducedUXs

--------------------------------------------------------------------------------

linkPolyL :: (Integral n, GaloisField n) => Occurrences -> PolyL n -> Either n (Poly n)
linkPolyL occurrences poly =
  let constant = PolyL.polyConstant poly
      limbPolynomial = IntMap.unionsWith (+) (fmap (uncurry (reindexLimb occurrences)) (PolyL.polyLimbs poly))
      varPolynomial = IntMap.fromList (map (first (reindexRef occurrences)) (Map.toList (PolyL.polyRefs poly)))
   in Poly.buildWithIntMap constant (IntMap.unionWith (+) limbPolynomial varPolynomial)

linkPolyLUnsafe :: (Integral n, GaloisField n) => Occurrences -> PolyL n -> Poly n
linkPolyLUnsafe occurrences xs = case linkPolyL occurrences xs of
  Left _ -> error "[ panic ] linkPolyLUnsafe: Left"
  Right p -> p

--------------------------------------------------------------------------------

reindexRef :: Occurrences -> Ref -> Var
reindexRef occurrences (F x) = reindexRefF occurrences x
reindexRef occurrences (B x) = reindexRefB occurrences x

reindexLimb :: (Integral n, GaloisField n) => Occurrences -> Limb -> n -> IntMap n
reindexLimb occurrences limb multiplier = case lmbSigns limb of
  Left sign ->
    -- precondition of `fromDistinctAscList` is that the keys are in ascending order
    IntMap.fromDistinctAscList
      [ ( reindexRefU
            occurrences
            (lmbRef limb)
            (i + lmbOffset limb),
          (2 ^ i) * if sign then multiplier else (-multiplier)
        )
        | i <- [0 .. lmbWidth limb - 1]
      ]
  Right signs ->
    -- precondition of `fromDistinctAscList` is that the keys are in ascending order
    IntMap.fromDistinctAscList
      [ ( reindexRefU
            occurrences
            (lmbRef limb)
            (i + lmbOffset limb),
          (2 ^ i) * if sign then multiplier else (-multiplier)
        )
        | (i, sign) <- zip [0 .. lmbWidth limb - 1] signs
      ]

reindexRefF :: Occurrences -> RefF -> Var
reindexRefF occurrences (RefFO x) = x + getOffset (occurCounters occurrences) (Output, ReadField)
reindexRefF occurrences (RefFI x) = x + getOffset (occurCounters occurrences) (PublicInput, ReadField)
reindexRefF occurrences (RefFP x) = x + getOffset (occurCounters occurrences) (PrivateInput, ReadField)
reindexRefF occurrences (RefFX x) = IntervalTable.reindex (indexTableF occurrences) x + getOffset (occurCounters occurrences) (Intermediate, ReadField)

reindexRefB :: Occurrences -> RefB -> Var
reindexRefB occurrences (RefBO x) = x + getOffset (occurCounters occurrences) (Output, ReadBool)
reindexRefB occurrences (RefBI x) = x + getOffset (occurCounters occurrences) (PublicInput, ReadBool)
reindexRefB occurrences (RefBP x) = x + getOffset (occurCounters occurrences) (PrivateInput, ReadBool)
reindexRefB occurrences (RefBX x) = IntervalTable.reindex (indexTableB occurrences) x + getOffset (occurCounters occurrences) (Intermediate, ReadBool)
reindexRefB occurrences (RefUBit _ x i) = reindexRefU occurrences x i

useNewLinker :: Bool
useNewLinker = False

reindexRefU :: Occurrences -> RefU -> Int -> Var
reindexRefU occurrences (RefUO w x) i = w * x + (i `mod` w) + getOffset (occurCounters occurrences) (Output, ReadAllUInts)
reindexRefU occurrences (RefUI w x) i = w * x + (i `mod` w) + getOffset (occurCounters occurrences) (PublicInput, ReadAllUInts)
reindexRefU occurrences (RefUP w x) i = w * x + (i `mod` w) + getOffset (occurCounters occurrences) (PrivateInput, ReadAllUInts)
reindexRefU occurrences (RefUX w x) i =
  let result =
        if useNewLinker
          then case IntMap.lookup w (indexTableUBWithOffsets occurrences) of
            Nothing -> error "[ panic ] reindexRefU: impossible"
            Just (offset, table) -> IntervalTable.reindex table (w * x + (i `mod` w)) + offset + getOffset (occurCounters occurrences) (Intermediate, ReadAllUInts)
          else
            let offset = getOffset (occurCounters occurrences) (Intermediate, ReadUInt w) + w * x
             in IntervalTable.reindex (indexTable occurrences) (offset - pinnedSize occurrences) + pinnedSize occurrences + (i `mod` w)
   in result

-------------------------------------------------------------------------------

-- | Allow us to determine which relations should be extracted from the pool
data Occurrences = Occurrences
  { occurCounters :: !Counters,
    refFsInOccurrencesF :: !IntSet,
    refBsInOccurrencesB :: !IntSet,
    refUsInOccurrencesU :: !(IntMap IntSet),
    refBsInOccurrencesUB :: !(IntMap IntervalTable),
    indexTableF :: !IntervalTable,
    indexTableB :: !IntervalTable,
    indexTableUBWithOffsets :: !(IntMap (Int, IntervalTable)),
    indexTable :: !IntervalTable,
    pinnedSize :: !Int
  }
  deriving (Show)

-- | Smart constructor for 'Occurrences'
constructOccurrences :: Counters -> OccurF -> OccurB -> OccurU -> OccurUB -> Occurrences
constructOccurrences counters occurF occurB occurU occurUB =
  let tablesUB = OccurUB.toIntervalTables occurUB
   in Occurrences
        { occurCounters = counters,
          refFsInOccurrencesF = OccurF.occuredSet occurF,
          refBsInOccurrencesB = OccurB.occuredSet occurB,
          refUsInOccurrencesU = OccurU.occuredSet occurU,
          refBsInOccurrencesUB = tablesUB,
          indexTableF = OccurF.toIntervalTable counters occurF,
          indexTableB = OccurB.toIntervalTable counters occurB,
          indexTableUBWithOffsets = OccurUB.toIntervalTablesWithOffsets occurUB,
          indexTable =
            OccurF.toIntervalTable counters occurF
              <> OccurB.toIntervalTable counters occurB
              <> OccurU.toIntervalTable counters occurU,
          pinnedSize = getCount counters Output + getCount counters PublicInput + getCount counters PrivateInput
        }
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}

module Keelung.Compiler.Linker
  ( linkConstraintModule,
    reindexRef,
    Env (..),
    constructEnv,
    toConstraints,
    reindexRefU,
    reindexRefF,
    reindexRefB,
  )
where

import Data.Bifunctor (Bifunctor (bimap, first))
import Data.Bits qualified
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
import Keelung.Compiler.Optimize.OccurB qualified as OccurB
import Keelung.Compiler.Optimize.OccurF qualified as OccurF
import Keelung.Compiler.Optimize.OccurU qualified as OccurU
import Keelung.Compiler.Optimize.OccurUB qualified as OccurUB
import Keelung.Compiler.Options
import Keelung.Compiler.Relations qualified as Relations
import Keelung.Compiler.Relations.Limb qualified as LimbRelations
import Keelung.Compiler.Relations.Reference qualified as RefRelations
import Keelung.Compiler.Relations.Slice qualified as SliceRelations
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
import Keelung.Data.Slice (Slice (..))
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Syntax.Counters

-------------------------------------------------------------------------------

linkConstraintModule :: (GaloisField n, Integral n) => ConstraintModule n -> ConstraintSystem n
linkConstraintModule cm =
  ConstraintSystem
    { csOptions = cmOptions cm,
      csCounters = updateCounters cm,
      csConstraints = constraints >>= linkConstraint env,
      csEqZeros = eqZeros,
      csDivMods = fmap (\(a, b, c, d) -> ([a], [b], [c], [d])) divMods,
      csCLDivMods = fmap (\(a, b, c, d) -> ([a], [b], [c], [d])) clDivMods,
      csModInvs = fmap (\(a, b, c, d) -> ([a], [b], [c], d)) modInvs
    }
  where
    !env = constructEnv cm
    -- constraints extracted from the constraint module
    constraints = toConstraints cm env

    -- constraints extracted from hints
    eqZeros = bimap (linkPolyLUnsafe env) (reindexRefF env) <$> cmEqZeros cm
    divMods = (\(a, b, q, r) -> (fromEitherRefU a, fromEitherRefU b, fromEitherRefU q, fromEitherRefU r)) <$> cmDivMods cm
    clDivMods = (\(a, b, q, r) -> (fromEitherRefU a, fromEitherRefU b, fromEitherRefU q, fromEitherRefU r)) <$> cmCLDivMods cm
    modInvs = (\(a, output, n, p) -> (fromEitherRefU a, fromEitherRefU output, fromEitherRefU n, toInteger p)) <$> cmModInvs cm

    fromEitherRefU :: Either RefU U -> (Width, Either Var Integer)
    fromEitherRefU (Left var) = let width = widthOf var in (width, Left (reindexRefB env (RefUBit var 0)))
    fromEitherRefU (Right val) = let width = widthOf val in (width, Right (toInteger val))

-------------------------------------------------------------------------------

-- | Predicate on whether a Limb should be exported as constraints
limbShouldBeKept :: Env -> Limb -> Bool
limbShouldBeKept env limb =
  if envUseNewLinker env
    then case lmbRef limb of
      RefUX width var -> case IntMap.lookup width (envRefBsInEnvUB env) of
        Nothing -> False
        Just table -> IntervalTable.member (width * var + lmbOffset limb, width * var + lmbOffset limb + lmbWidth limb) table
      _ -> True -- it's a pinned UInt variable
    else refUShouldBeKept env (lmbRef limb)

-- | Predicate on whether a RefU should be exported as constraints
refUShouldBeKept :: Env -> RefU -> Bool
refUShouldBeKept env ref = case ref of
  RefUX width var ->
    -- it's a UInt intermediate variable that occurs in the circuit
    ( case IntMap.lookup width (envRefUsInEnvU env) of
        Nothing -> False
        Just xs -> IntSet.member var xs
    )
  _ -> True -- it's a pinned UInt variable

shouldBeKept :: Env -> Ref -> Bool
shouldBeKept env (F ref) = case ref of
  RefFX var ->
    -- it's a Field intermediate variable that occurs in the circuit
    var `IntSet.member` envRefFsInEnvF env
  _ -> True -- it's a pinned Field variable
shouldBeKept env (B ref) = case ref of
  RefBX var ->
    --  it's a Boolean intermediate variable that occurs in the circuit
    var `IntSet.member` envRefBsInEnvB env
  RefUBit var i ->
    if envUseNewLinker env
      then refUBitShouldBeKept var i
      else --  it's a Bit test of a UInt intermediate variable that occurs in the circuit
        refUShouldBeKept env var
  _ -> True -- it's a pinned Field variable
  where
    refUBitShouldBeKept :: RefU -> Int -> Bool
    refUBitShouldBeKept refU i = case refU of
      RefUX width var ->
        if envUseNewLinker env
          then case IntMap.lookup width (envRefBsInEnvUB env) of
            Nothing -> False
            Just table -> IntervalTable.member (width * var + i, width * var + i + 1) table
          else refUShouldBeKept env refU
      _ -> True -- it's a pinned UInt variable

-------------------------------------------------------------------------------

-- | Link a specialized constraint to a list of constraints
linkConstraint :: (GaloisField n, Integral n) => Env -> Constraint n -> Seq (Linked.Constraint n)
linkConstraint env (CAddL as) = Seq.fromList [Linked.CAdd (linkPolyLUnsafe env as)]
linkConstraint env (CRefEq x y) =
  case Poly.buildEither 0 [(reindexRef env x, 1), (reindexRef env y, -1)] of
    Left _ -> error "CRefEq: two references are the same"
    Right xs -> Seq.fromList [Linked.CAdd xs]
linkConstraint env (CRefBNEq x y) =
  case Poly.buildEither 1 [(reindexRefB env x, -1), (reindexRefB env y, -1)] of
    Left _ -> error "CRefBNEq: two variables are the same"
    Right xs -> Seq.fromList [Linked.CAdd xs]
linkConstraint env (CLimbEq x y) =
  if lmbWidth x /= lmbWidth y
    then error "[ panic ] CLimbEq: Limbs are of different width"
    else do
      case FieldInfo.fieldTypeData (envFieldInfo env) of
        Binary _ -> do
          i <- Seq.fromList [0 .. lmbWidth x - 1]
          let pair = [(reindexRefU env (lmbRef x) (lmbOffset x + i), 1), (reindexRefU env (lmbRef y) (lmbOffset y + i), -1)]
          case Poly.buildEither 0 pair of
            Left _ -> error "CLimbEq: two variables are the same"
            Right xs -> Seq.fromList [Linked.CAdd xs]
        Prime _ -> do
          let pairsX = reindexLimb env x 1
          let pairsY = reindexLimb env y (-1)
          let pairs = IntMap.unionWith (+) pairsX pairsY
          case Poly.buildWithIntMap 0 pairs of
            Left _ -> error "CLimbEq: two variables are the same"
            Right xs -> Seq.fromList [Linked.CAdd xs]
linkConstraint env (CRefUEq x y) =
  -- split `x` and `y` into smaller limbs and pair them up with `CLimbEq`
  let cVarEqLs = Seq.fromList $ zipWith CLimbEq (Limb.refUToLimbs (envFieldWidth env) x) (Limb.refUToLimbs (envFieldWidth env) y)
   in cVarEqLs >>= linkConstraint env
linkConstraint env (CSliceEq x y) =
  let widthX = Slice.sliceEnd x - Slice.sliceStart x
      widthY = Slice.sliceEnd y - Slice.sliceStart y
   in if widthX /= widthY
        then error "[ panic ] CSliceEq: Slices are of different width"
        else
          let width = envFieldWidth env
              -- split both Slices into smaller chunks of size `width`
              pairs =
                Seq.fromList $
                  [ ( Slice (sliceRefU x) (sliceStart x + i) ((sliceStart x + i + width) `min` sliceEnd x),
                      Slice (sliceRefU y) (sliceStart y + i) ((sliceStart y + i + width) `min` sliceEnd y)
                    )
                    | i <- [0, width .. widthOf x - 1]
                  ]
           in pairs >>= \(sliceX, sliceY) ->
                let sliceX' = reindexSlice env sliceX True
                    sliceY' = reindexSlice env sliceY False
                 in case Poly.buildWithIntMap 0 (IntMap.unionWith (+) sliceX' sliceY') of
                      Left _ -> error "CSliceEq: impossible"
                      Right xs -> Seq.fromList [Linked.CAdd xs]
linkConstraint env (CRefFVal x n) = case Poly.buildEither (-n) [(reindexRef env x, 1)] of
  Left _ -> error "CRefFVal: impossible"
  Right xs -> Seq.fromList [Linked.CAdd xs]
linkConstraint env (CLimbVal x n) =
  -- "ArithException: arithmetic underflow" will be thrown if `n` is negative in Binary fields
  let negatedConstant = case FieldInfo.fieldTypeData (envFieldInfo env) of
        Prime _ -> fromInteger (-n)
        Binary _ -> fromInteger n
   in case Poly.buildWithIntMap negatedConstant (reindexLimb env x 1) of
        Left _ -> error "CLimbVal: impossible"
        Right xs -> Seq.fromList [Linked.CAdd xs]
linkConstraint env (CRefUVal x n) =
  case FieldInfo.fieldTypeData (envFieldInfo env) of
    Binary _ ->
      let cRefFVals = Seq.fromList [CRefFVal (B (RefUBit x i)) (if Data.Bits.testBit n i then 1 else 0) | i <- [0 .. widthOf x - 1]]
       in cRefFVals >>= linkConstraint env
    Prime _ -> do
      -- split the Integer into smaller chunks of size `fieldWidth`
      let number = U.new (widthOf x) n
          chunks = map toInteger (U.chunks (envFieldWidth env) number)
          cLimbVals = Seq.fromList $ zipWith CLimbVal (Limb.refUToLimbs (envFieldWidth env) x) chunks
       in cLimbVals >>= linkConstraint env
linkConstraint env (CSliceVal x n) =
  let constant = case FieldInfo.fieldTypeData (envFieldInfo env) of
        Binary _ -> fromInteger (if n < 0 then -n else n)
        Prime _ -> fromInteger n
      width = envFieldWidth env
      -- split `n` into smaller chunks of size `width`
      constantChunks = zip [0 ..] (U.chunks (envFieldWidth env) (U.new (widthOf x) constant))
      pairs = Seq.fromList [(Slice (sliceRefU x) (sliceStart x + width * i) ((sliceStart x + width * (i + 1)) `min` sliceEnd x), chunk) | (i, chunk) <- constantChunks]
   in pairs >>= \(slice, c) ->
        case Poly.buildWithIntMap (fromIntegral c) (reindexSlice env slice False) of
          Left _ -> error "CSliceVal: impossible"
          Right xs -> Seq.fromList [Linked.CAdd xs]
linkConstraint env (CMulL as bs cs) =
  Seq.fromList
    [ Linked.CMul
        (linkPolyLUnsafe env as)
        (linkPolyLUnsafe env bs)
        ( case cs of
            Left n -> Left n
            Right xs -> linkPolyL env xs
        )
    ]

updateCounters :: ConstraintModule n -> Counters
updateCounters cm =
  if optUseNewLinker (cmOptions cm)
    then updateCountersNew (OccurF.occuredSet (cmOccurrenceF cm)) (OccurB.occuredSet (cmOccurrenceB cm)) (OccurUB.toIntervalTables (cmOccurrenceUB cm)) (cmCounters cm)
    else updateCountersOld (OccurF.occuredSet (cmOccurrenceF cm)) (OccurB.occuredSet (cmOccurrenceB cm)) (OccurU.occuredSet (cmOccurrenceU cm)) (cmCounters cm)
  where
    updateCountersOld :: IntSet -> IntSet -> IntMap IntSet -> Counters -> Counters
    updateCountersOld refFsInEnvF refBsInEnvB refUsInEnvU counters =
      let newFXCount = (WriteField, IntSet.size refFsInEnvF)
          newBXCount = (WriteBool, IntSet.size refBsInEnvB)
          newUXCounts = IntMap.mapWithKey (\width set -> (WriteUInt width, IntSet.size set)) refUsInEnvU
          actions = newFXCount : newBXCount : IntMap.elems newUXCounts
       in foldr (\(selector, count) -> setCount (Intermediate, selector) count) counters actions

    updateCountersNew :: IntSet -> IntSet -> IntMap IntervalTable -> Counters -> Counters
    updateCountersNew refFsInEnvF refBsInEnvB refBsInEnvUB =
      setCount (Intermediate, WriteField) (IntSet.size refFsInEnvF)
        . setCount (Intermediate, WriteBool) (IntSet.size refBsInEnvB)
        . setCountOfIntermediateUIntBits (fmap IntervalTable.size refBsInEnvUB)

--------------------------------------------------------------------------------

linkPolyL :: (Integral n, GaloisField n) => Env -> PolyL n -> Either n (Poly n)
linkPolyL env poly =
  let constant = PolyL.polyConstant poly
      limbPolynomial = IntMap.unionsWith (+) (fmap (uncurry (reindexLimb env)) (PolyL.polyLimbs poly))
      varPolynomial = IntMap.fromList (map (first (reindexRef env)) (Map.toList (PolyL.polyRefs poly)))
   in -- traceShow (fmap N poly, fmap N limbPolynomial)
      Poly.buildWithIntMap constant (IntMap.unionWith (+) limbPolynomial varPolynomial)

linkPolyLUnsafe :: (Integral n, GaloisField n) => Env -> PolyL n -> Poly n
linkPolyLUnsafe env xs = case linkPolyL env xs of
  Left _ -> error "[ panic ] linkPolyLUnsafe: Left"
  Right p -> p

--------------------------------------------------------------------------------

reindexRef :: Env -> Ref -> Var
reindexRef env (F x) = reindexRefF env x
reindexRef env (B x) = reindexRefB env x

reindexLimb :: (Integral n, GaloisField n) => Env -> Limb -> n -> IntMap n
reindexLimb env limb multiplier = case lmbSigns limb of
  Left sign ->
    -- precondition of `fromDistinctAscList` is that the keys are in ascending order
    IntMap.fromDistinctAscList
      [ ( reindexRefU
            env
            (lmbRef limb)
            (i + lmbOffset limb),
          2 ^ i * if sign then multiplier else (-multiplier)
        )
        | i <- [0 .. lmbWidth limb - 1]
      ]
  Right signs ->
    -- precondition of `fromDistinctAscList` is that the keys are in ascending order
    IntMap.fromDistinctAscList
      [ ( reindexRefU
            env
            (lmbRef limb)
            (i + lmbOffset limb),
          2 ^ i * if sign then multiplier else (-multiplier)
        )
        | (i, sign) <- zip [0 .. lmbWidth limb - 1] signs
      ]

reindexSlice :: (Integral n, GaloisField n) => Env -> Slice -> Bool -> IntMap n
reindexSlice env slice sign =
  -- precondition of `fromDistinctAscList` is that the keys are in ascending order
  IntMap.fromDistinctAscList
    [ ( reindexRefU
          env
          (Slice.sliceRefU slice)
          (Slice.sliceStart slice + i),
        if sign then 2 ^ i else -(2 ^ i)
      )
      | i <- [0 .. Slice.sliceEnd slice - Slice.sliceStart slice - 1]
    ]

reindexRefF :: Env -> RefF -> Var
reindexRefF env (RefFO x) = x + getOffset (envOldCounters env) (Output, ReadField)
reindexRefF env (RefFI x) = x + getOffset (envOldCounters env) (PublicInput, ReadField)
reindexRefF env (RefFP x) = x + getOffset (envOldCounters env) (PrivateInput, ReadField)
reindexRefF env (RefFX x) = IntervalTable.reindex (envIndexTableF env) x + getOffset (envOldCounters env) (Intermediate, ReadField)

reindexRefB :: Env -> RefB -> Var
reindexRefB env (RefBO x) = x + getOffset (envOldCounters env) (Output, ReadBool)
reindexRefB env (RefBI x) = x + getOffset (envOldCounters env) (PublicInput, ReadBool)
reindexRefB env (RefBP x) = x + getOffset (envOldCounters env) (PrivateInput, ReadBool)
reindexRefB env (RefBX x) = IntervalTable.reindex (envIndexTableB env) x + getOffset (envOldCounters env) (Intermediate, ReadBool)
reindexRefB env (RefUBit x i) = reindexRefU env x i

reindexRefU :: Env -> RefU -> Int -> Var
reindexRefU env (RefUO w x) i = w * x + i `mod` w + getOffset (envOldCounters env) (Output, ReadAllUInts)
reindexRefU env (RefUI w x) i = w * x + i `mod` w + getOffset (envOldCounters env) (PublicInput, ReadAllUInts)
reindexRefU env (RefUP w x) i = w * x + i `mod` w + getOffset (envOldCounters env) (PrivateInput, ReadAllUInts)
reindexRefU env (RefUX w x) i =
  let result =
        if envUseNewLinker env
          then case IntMap.lookup w (envIndexTableUBWithOffsets env) of
            Nothing -> error "[ panic ] reindexRefU: impossible"
            Just (offset, table) -> IntervalTable.reindex table (w * x + i `mod` w) + offset + getOffset (envNewCounters env) (Intermediate, ReadAllUInts)
          else
            let offset = getOffset (envOldCounters env) (Intermediate, ReadUInt w) + w * x
             in IntervalTable.reindex (envIndexTable env) (offset - envPinnedSize env) + envPinnedSize env + i `mod` w
   in result

-------------------------------------------------------------------------------

-- | Extract Constraints from a ConstraintModule
toConstraints :: (GaloisField n, Integral n) => ConstraintModule n -> Env -> Seq (Constraint n)
toConstraints cm env =
  let -- constraints extracted from relations between Refs
      refConstraints = RefRelations.toConstraints (shouldBeKept env) (Relations.relationsR (cmRelations cm))
      -- constraints extracted from relations between Slices (only when optUseUIntUnionFind = True)
      sliceConstraints =
        if optUseNewLinker (cmOptions cm)
          then SliceRelations.toConstraintsWithNewLinker (cmOccurrenceUB cm) (refUShouldBeKept env) (Relations.relationsS (cmRelations cm))
          else SliceRelations.toConstraints (refUShouldBeKept env) (Relations.relationsS (cmRelations cm))
      -- constraints extracted from relations between UInts & Limbs (only when optUseUIntUnionFind = False)
      limbAndUIntConstraints =
        LimbRelations.toConstraints (limbShouldBeKept env) (Relations.relationsL (cmRelations cm))
          <> UIntRelations.toConstraints (refUShouldBeKept env) (Relations.relationsU (cmRelations cm))
      -- constraints extracted from addative constraints
      fromAddativeConstraints = fmap CAddL (cmAddL cm)
      -- constraints extracted from multiplicative constraints
      fromMultiplicativeConstraints = fmap (\(a, b, c) -> CMulL a b c) (cmMulL cm)
   in refConstraints
        <> ( if optUseUIntUnionFind (cmOptions cm)
               then sliceConstraints
               else limbAndUIntConstraints
           )
        <> fromAddativeConstraints
        <> fromMultiplicativeConstraints

-------------------------------------------------------------------------------

-- | Allow us to determine which relations should be extracted from the pool
data Env = Env
  { envOldCounters :: !Counters,
    envNewCounters :: !Counters,
    envRefFsInEnvF :: !IntSet,
    envRefBsInEnvB :: !IntSet,
    envRefUsInEnvU :: !(IntMap IntSet),
    envRefBsInEnvUB :: !(IntMap IntervalTable),
    envIndexTableF :: !IntervalTable,
    envIndexTableB :: !IntervalTable,
    envIndexTableUBWithOffsets :: !(IntMap (Int, IntervalTable)),
    envIndexTable :: !IntervalTable,
    envPinnedSize :: !Int,
    -- field related
    envFieldInfo :: !FieldInfo,
    envFieldWidth :: !Width,
    -- other options
    envUseNewLinker :: !Bool,
    envUseUIntUnionFind :: !Bool
  }
  deriving (Show)

-- | Smart constructor for 'Env'
constructEnv :: ConstraintModule n -> Env
constructEnv cm =
  let tablesUB = OccurUB.toIntervalTables (cmOccurrenceUB cm)
   in Env
        { envOldCounters = cmCounters cm,
          envNewCounters = updateCounters cm,
          envRefFsInEnvF = OccurF.occuredSet (cmOccurrenceF cm),
          envRefBsInEnvB = OccurB.occuredSet (cmOccurrenceB cm),
          envRefUsInEnvU = OccurU.occuredSet (cmOccurrenceU cm),
          envRefBsInEnvUB = tablesUB,
          envIndexTableF = OccurF.toIntervalTable (cmCounters cm) (cmOccurrenceF cm),
          envIndexTableB = OccurB.toIntervalTable (cmCounters cm) (cmOccurrenceB cm),
          envIndexTableUBWithOffsets = OccurUB.toIntervalTablesWithOffsets (cmOccurrenceUB cm),
          envIndexTable =
            OccurF.toIntervalTable (cmCounters cm) (cmOccurrenceF cm)
              <> OccurB.toIntervalTable (cmCounters cm) (cmOccurrenceB cm)
              <> OccurU.toIntervalTable (cmCounters cm) (cmOccurrenceU cm),
          envPinnedSize = getCount (cmCounters cm) Output + getCount (cmCounters cm) PublicInput + getCount (cmCounters cm) PrivateInput,
          envFieldInfo = optFieldInfo (cmOptions cm),
          envFieldWidth = FieldInfo.fieldWidth (optFieldInfo (cmOptions cm)),
          envUseNewLinker = optUseNewLinker (cmOptions cm),
          envUseUIntUnionFind = optUseUIntUnionFind (cmOptions cm)
        }
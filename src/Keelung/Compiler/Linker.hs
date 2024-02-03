{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}

module Keelung.Compiler.Linker (linkConstraintModule, reindexRef, Env, constructEnv, updateCounters, coverageIsValid) where

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
import Data.Set (Set)
import Data.Set qualified as Set
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
      csCounters = counters,
      csConstraints =
        fromRefRelations
          <> ( if optUseUIntUnionFind (cmOptions cm)
                 then fromSliceRelations
                 else fromUIntAndLimbRelations
             )
          <> fromAddativeConstraints
          <> fromMultiplicativeConstraints,
      csEqZeros = eqZeros,
      csDivMods = fmap (\(a, b, c, d) -> ([a], [b], [c], [d])) divMods,
      csCLDivMods = fmap (\(a, b, c, d) -> ([a], [b], [c], [d])) clDivMods,
      csModInvs = fmap (\(a, b, c, d) -> ([a], [b], [c], d)) modInvs
    }
  where
    -- new counters after linking
    !counters = updateCounters cm

    !env = constructEnv (cmOptions cm) (cmCounters cm) counters (cmOccurrenceF cm) (cmOccurrenceB cm) (cmOccurrenceU cm) (cmOccurrenceUB cm)
    uncurry3 f (a, b, c) = f a b c

    -- constraints extracted from relations between Refs
    fromRefRelations = RefRelations.toConstraints (shouldBeKept env) (Relations.relationsR (cmRelations cm)) >>= linkConstraint env

    -- constraints extracted from relations between UInts & Limbs (only when optUseUIntUnionFind = False)
    fromUIntAndLimbRelations :: (GaloisField n, Integral n) => Seq (Linked.Constraint n)
    fromUIntAndLimbRelations =
      (LimbRelations.toConstraints (limbShouldBeKept env) (Relations.relationsL (cmRelations cm)) >>= linkConstraint env)
        <> (UIntRelations.toConstraints (refUShouldBeKept env) (Relations.relationsU (cmRelations cm)) >>= linkConstraint env)

    -- constraints extracted from relations between Slices (only when optUseUIntUnionFind = True)
    fromSliceRelations :: (GaloisField n, Integral n) => Seq (Linked.Constraint n)
    fromSliceRelations =
      if envUseNewLinker env
        then SliceRelations.toConstraintsWithNewLinker (cmOccurrenceUB cm) (refUShouldBeKept env) (Relations.relationsS (cmRelations cm)) >>= linkConstraint env
        else SliceRelations.toConstraints (refUShouldBeKept env) (Relations.relationsS (cmRelations cm)) >>= linkConstraint env

    -- constraints extracted from specialized constraints
    fromAddativeConstraints = linkConstraint env . CAddL =<< cmAddL cm
    fromMultiplicativeConstraints = linkConstraint env . uncurry3 CMulL =<< cmMulL cm
    eqZeros = bimap (linkPolyLUnsafe env) (reindexRefF env) <$> cmEqZeros cm

    -- constraints extracted from hints
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
   in Poly.buildWithIntMap constant (IntMap.unionWith (+) limbPolynomial varPolynomial)

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
constructEnv :: Options -> Counters -> Counters -> OccurF -> OccurB -> OccurU -> OccurUB -> Env
constructEnv options oldCounters newCounters occurF occurB occurU occurUB =
  let tablesUB = OccurUB.toIntervalTables occurUB
   in Env
        { envOldCounters = oldCounters,
          envNewCounters = newCounters,
          envRefFsInEnvF = OccurF.occuredSet occurF,
          envRefBsInEnvB = OccurB.occuredSet occurB,
          envRefUsInEnvU = OccurU.occuredSet occurU,
          envRefBsInEnvUB = tablesUB,
          envIndexTableF = OccurF.toIntervalTable oldCounters occurF,
          envIndexTableB = OccurB.toIntervalTable oldCounters occurB,
          envIndexTableUBWithOffsets = OccurUB.toIntervalTablesWithOffsets occurUB,
          envIndexTable =
            OccurF.toIntervalTable oldCounters occurF
              <> OccurB.toIntervalTable oldCounters occurB
              <> OccurU.toIntervalTable oldCounters occurU,
          envPinnedSize = getCount oldCounters Output + getCount oldCounters PublicInput + getCount oldCounters PrivateInput,
          envFieldInfo = optFieldInfo options,
          envFieldWidth = FieldInfo.fieldWidth (optFieldInfo options),
          envUseNewLinker = optUseNewLinker options,
          envUseUIntUnionFind = optUseUIntUnionFind options
        }

--------------------------------------------------------------------------------

-- | Datatype for keeping track of which Ref is mapped to which Var
newtype Coverage = Coverage (IntMap (Set Ref))

-- | A Coverage is valid if:
--      1. no Var is skipped, i.e. there are no gaps in the IntMap
--      3. no Var is mapped to multiple Refs
coverageIsValid :: Coverage -> Bool
coverageIsValid (Coverage xs) =
  let noSkipped = case IntMap.maxViewWithKey xs of
        Nothing -> True -- empty IntMap
        Just ((k, _), _) -> k == IntMap.size xs - 1
      noMultipleRefs = all (\s -> Set.size s == 1) xs
   in noSkipped && noMultipleRefs

-- | How to combine two coverages
instance Semigroup Coverage where
  Coverage a <> Coverage b = Coverage (IntMap.unionWith (<>) a b)

-- | The empty coverage
instance Monoid Coverage where
  mempty = Coverage IntMap.empty

-- | Typeclass for generating Coverage reports
class GenerateCoverage a where
  generateCoverage :: Env -> a -> Coverage

instance GenerateCoverage Limb where
  generateCoverage env limb =
    Coverage $
      -- precondition of `fromDistinctAscList` is that the keys are in ascending order
      IntMap.fromDistinctAscList
        [ ( reindexRefU
              env
              (lmbRef limb)
              (i + lmbOffset limb),
            Set.singleton (B (RefUBit (lmbRef limb) i))
          )
          | i <- [0 .. lmbWidth limb - 1]
        ]

instance GenerateCoverage Slice where
  generateCoverage env slice =
    Coverage $
      -- precondition of `fromDistinctAscList` is that the keys are in ascending order
      IntMap.fromDistinctAscList
        [ ( reindexRefU
              env
              (Slice.sliceRefU slice)
              i,
            Set.singleton (B (RefUBit (Slice.sliceRefU slice) i))
          )
          | i <- [Slice.sliceStart slice .. Slice.sliceEnd slice - 1]
        ]

instance (GenerateCoverage a) => GenerateCoverage (Seq a) where
  generateCoverage env xs = mconcat $ map (generateCoverage env) (toList xs)

instance (GenerateCoverage a) => GenerateCoverage [a] where
  generateCoverage env xs = mconcat $ map (generateCoverage env) xs

instance GenerateCoverage RefF where
  generateCoverage env ref = Coverage $ IntMap.singleton (reindexRefF env ref) (Set.singleton (F ref))

instance GenerateCoverage RefB where
  generateCoverage env ref = Coverage $ IntMap.singleton (reindexRefB env ref) (Set.singleton (B ref))

instance GenerateCoverage Ref where
  generateCoverage env (F refF) = generateCoverage env refF
  generateCoverage env (B refB) = generateCoverage env refB

instance GenerateCoverage RefU where
  generateCoverage env refU = generateCoverage env (Limb.refUToLimbs (envFieldWidth env) refU)

instance GenerateCoverage (PolyL n) where
  generateCoverage env poly =
    let limbCoverage = generateCoverage env (fmap fst (PolyL.polyLimbs poly))
        refCoverage = generateCoverage env (Map.keys (PolyL.polyRefs poly))
     in limbCoverage <> refCoverage

instance GenerateCoverage (Constraint n) where
  generateCoverage env (CAddL poly) = generateCoverage env poly
  generateCoverage env (CRefEq x y) = generateCoverage env x <> generateCoverage env y
  generateCoverage env (CRefBNEq x y) = generateCoverage env x <> generateCoverage env y
  generateCoverage env (CLimbEq x y) = generateCoverage env x <> generateCoverage env y
  generateCoverage env (CRefUEq x y) = generateCoverage env x <> generateCoverage env y
  generateCoverage env (CSliceEq x y) = generateCoverage env x <> generateCoverage env y
  generateCoverage env (CRefFVal x _) = generateCoverage env x
  generateCoverage env (CLimbVal x _) = generateCoverage env x
  generateCoverage env (CRefUVal x _) = generateCoverage env x
  generateCoverage env (CMulL a b (Left _)) = generateCoverage env a <> generateCoverage env b
  generateCoverage env (CMulL a b (Right c)) = generateCoverage env a <> generateCoverage env b <> generateCoverage env c
  generateCoverage env (CSliceVal x _) = generateCoverage env x

instance GenerateCoverage (Either RefU U) where
  generateCoverage env (Left refU) = generateCoverage env refU
  generateCoverage _ (Right _) = mempty

instance (Integral n, GaloisField n) => GenerateCoverage (ConstraintModule n) where
  generateCoverage env cm =
    let refConstraints = RefRelations.toConstraints (shouldBeKept env) (Relations.relationsR (cmRelations cm))

        sliceRelations = SliceRelations.toConstraints (refUShouldBeKept env) (Relations.relationsS (cmRelations cm))
        limbAndUIntRelations =
          LimbRelations.toConstraints (limbShouldBeKept env) (Relations.relationsL (cmRelations cm))
            <> UIntRelations.toConstraints (refUShouldBeKept env) (Relations.relationsU (cmRelations cm))

        fromMultiplicativeConstraints (a, b, Left _) = generateCoverage env a <> generateCoverage env b
        fromMultiplicativeConstraints (a, b, Right c) = generateCoverage env a <> generateCoverage env b <> generateCoverage env c
        fromModInvs (a, b, c, _) = generateCoverage env a <> generateCoverage env b <> generateCoverage env c
        fromCLDivMods (a, b, c, d) = generateCoverage env a <> generateCoverage env b <> generateCoverage env c <> generateCoverage env d
        fromDivMods (a, b, c, d) = generateCoverage env a <> generateCoverage env b <> generateCoverage env c <> generateCoverage env d
        fromEqZeros (a, b) = generateCoverage env a <> generateCoverage env b
     in mconcat $
          toList $
            fmap (generateCoverage env) refConstraints
              <> ( if optUseUIntUnionFind (cmOptions cm)
                     then fmap (generateCoverage env) sliceRelations
                     else fmap (generateCoverage env) limbAndUIntRelations
                 )
              <> fmap (generateCoverage env) (cmAddL cm)
              <> fmap fromMultiplicativeConstraints (cmMulL cm)
              <> fmap fromEqZeros (cmEqZeros cm)
              <> fmap fromDivMods (cmDivMods cm)
              <> fmap fromCLDivMods (cmCLDivMods cm)
              <> fmap fromModInvs (cmModInvs cm)
{-# LANGUAGE BangPatterns #-}

module Keelung.Compiler.Linker (linkConstraintModule, reindexRef, Env, constructEnv) where

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
import Keelung.Compiler.Options
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
    { csOptions = cmOptions cm,
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
    !env = constructEnv (cmOptions cm) (cmCounters cm) (cmOccurrenceF cm) (cmOccurrenceB cm) (cmOccurrenceU cm) (cmOccurrenceUB cm)
    !counters = updateCounters env (cmCounters cm)
    uncurry3 f (a, b, c) = f a b c

    -- fieldWidth = FieldInfo.fieldWidth ((optFieldInfo . cmOptions) cm)

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
       in Seq.fromList (linkConstraint env =<< result)

    shouldBeKept :: Ref -> Bool
    shouldBeKept (F ref) = refFShouldBeKept ref
    shouldBeKept (B ref) = refBShouldBeKept ref

    refFShouldBeKept :: RefF -> Bool
    refFShouldBeKept ref = case ref of
      RefFX var ->
        -- it's a Field intermediate variable that occurs in the circuit
        var `IntSet.member` envRefFsInEnvF env
      _ ->
        -- it's a pinned Field variable
        True

    refUShouldBeKept :: RefU -> Bool
    refUShouldBeKept ref = case ref of
      RefUX width var ->
        -- it's a UInt intermediate variable that occurs in the circuit
        ( case IntMap.lookup width (envRefUsInEnvU env) of
            Nothing -> False
            Just xs -> IntSet.member var xs
        )
      _ ->
        -- it's a pinned UInt variable
        True

    limbShouldBeKept :: Limb -> Bool
    limbShouldBeKept limb =
      if envUseNewLinker env
        then case lmbRef limb of
          RefUX width var -> case IntMap.lookup width (envRefBsInEnvUB env) of
            Nothing -> False
            Just table -> IntervalTable.member (width * var + lmbOffset limb, width * var + lmbOffset limb + lmbWidth limb) table
          _ -> True -- it's a pinned UInt variable
        else refUShouldBeKept (lmbRef limb)

    refUBitShouldBeKept :: RefU -> Int -> Bool
    refUBitShouldBeKept refU i = case refU of
      RefUX width var ->
        if envUseNewLinker env
          then case IntMap.lookup width (envRefBsInEnvUB env) of
            Nothing -> False
            Just table -> IntervalTable.member (width * var + i, width * var + i + 1) table
          else refUShouldBeKept refU
      _ -> True -- it's a pinned UInt variable
    refBShouldBeKept :: RefB -> Bool
    refBShouldBeKept ref = case ref of
      RefBX var ->
        --  it's a Boolean intermediate variable that occurs in the circuit
        var `IntSet.member` envRefBsInEnvB env
      -- \|| RefBX var `Set.member` refBsInEnvF env
      RefUBit _ var i ->
        if envUseNewLinker env
          then refUBitShouldBeKept var i
          else --  it's a Bit test of a UInt intermediate variable that occurs in the circuit
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
       in Seq.fromList (linkConstraint env =<< result)

    extractUIntRelations :: (GaloisField n, Integral n) => UIntRelations -> Seq (Linked.Constraint n)
    extractUIntRelations relations = UIntRelations.toConstraints refUShouldBeKept relations >>= Seq.fromList . linkConstraint env

    varEqFs = extractRefRelations (cmRelations cm)
    varEqLs = extractLimbRelations (Relations.exportLimbRelations (cmRelations cm))
    varEqUs = extractUIntRelations (Relations.exportUIntRelations (cmRelations cm))

    addLs = Seq.fromList $ linkConstraint env . CAddL =<< cmAddL cm
    mulLs = Seq.fromList $ linkConstraint env . uncurry3 CMulL =<< cmMulL cm
    eqZeros = Seq.fromList $ map (bimap (linkPolyLUnsafe env) (reindexRefF env)) $ cmEqZeros cm

    fromEitherRefU :: Either RefU U -> (Width, Either Var Integer)
    fromEitherRefU (Left var) = let width = widthOf var in (width, Left (reindexRefB env (RefUBit width var 0)))
    fromEitherRefU (Right val) = let width = widthOf val in (width, Right (U.uValue val))

    divMods = map (\(a, b, q, r) -> (fromEitherRefU a, fromEitherRefU b, fromEitherRefU q, fromEitherRefU r)) $ cmDivMods cm
    clDivMods = map (\(a, b, q, r) -> (fromEitherRefU a, fromEitherRefU b, fromEitherRefU q, fromEitherRefU r)) $ cmCLDivMods cm
    modInvs = map (\(a, output, n, p) -> (fromEitherRefU a, fromEitherRefU output, fromEitherRefU n, U.uValue p)) $ cmModInvs cm

-------------------------------------------------------------------------------

-- | Link a specialized constraint to a list of constraints
linkConstraint :: (GaloisField n, Integral n) => Env -> Constraint n -> [Linked.Constraint n]
linkConstraint env (CAddL as) = [Linked.CAdd (linkPolyLUnsafe env as)]
linkConstraint env (CRefEq x y) =
  case Poly.buildEither 0 [(reindexRef env x, 1), (reindexRef env y, -1)] of
    Left _ -> error "CRefEq: two references are the same"
    Right xs -> [Linked.CAdd xs]
linkConstraint env (CRefBNEq x y) =
  case Poly.buildEither 1 [(reindexRefB env x, -1), (reindexRefB env y, -1)] of
    Left _ -> error "CRefBNEq: two variables are the same"
    Right xs -> [Linked.CAdd xs]
linkConstraint env (CLimbEq x y) =
  if lmbWidth x /= lmbWidth y
    then error "[ panic ] CLimbEq: Limbs are of different width"
    else do
      case FieldInfo.fieldTypeData (envFieldInfo env) of
        Binary _ -> do
          i <- [0 .. lmbWidth x - 1]
          let pair = [(reindexRefU env (lmbRef x) (lmbOffset x + i), 1), (reindexRefU env (lmbRef y) (lmbOffset y + i), -1)]
          case Poly.buildEither 0 pair of
            Left _ -> error "CLimbEq: two variables are the same"
            Right xs -> [Linked.CAdd xs]
        Prime _ -> do
          let pairsX = reindexLimb env x 1
          let pairsY = reindexLimb env y (-1)
          let pairs = IntMap.unionWith (+) pairsX pairsY
          case Poly.buildWithIntMap 0 pairs of
            Left _ -> error "CLimbEq: two variables are the same"
            Right xs -> [Linked.CAdd xs]
linkConstraint env (CRefUEq x y) =
  -- split `x` and `y` into smaller limbs and pair them up with `CLimbEq`
  let cVarEqLs = zipWith CLimbEq (Limb.refUToLimbs (envFieldWidth env) x) (Limb.refUToLimbs (envFieldWidth env) y)
   in cVarEqLs >>= linkConstraint env
linkConstraint env (CRefFVal x n) = case Poly.buildEither (-n) [(reindexRef env x, 1)] of
  Left _ -> error "CRefFVal: impossible"
  Right xs -> [Linked.CAdd xs]
linkConstraint env (CLimbVal x n) =
  -- "ArithException: arithmetic underflow" will be thrown if `n` is negative in Binary fields
  let negatedConstant = case FieldInfo.fieldTypeData (envFieldInfo env) of
        Prime _ -> fromInteger (-n)
        Binary _ -> fromInteger n
   in case Poly.buildWithIntMap negatedConstant (reindexLimb env x 1) of
        Left _ -> error "CLimbVal: impossible"
        Right xs -> [Linked.CAdd xs]
linkConstraint env (CRefUVal x n) =
  case FieldInfo.fieldTypeData (envFieldInfo env) of
    Binary _ ->
      let width = widthOf x
          cRefFVals = [CRefFVal (B (RefUBit width x i)) (if Data.Bits.testBit n i then 1 else 0) | i <- [0 .. widthOf x - 1]]
       in cRefFVals >>= linkConstraint env
    Prime _ -> do
      -- split the Integer into smaller chunks of size `fieldWidth`
      let number = U.new (widthOf x) n
          chunks = map U.uValue (U.chunks (envFieldWidth env) number)
          cLimbVals = zipWith CLimbVal (Limb.refUToLimbs (envFieldWidth env) x) chunks
       in cLimbVals >>= linkConstraint env
linkConstraint env (CMulL as bs cs) =
  [ Linked.CMul
      (linkPolyLUnsafe env as)
      (linkPolyLUnsafe env bs)
      ( case cs of
          Left n -> Left n
          Right xs -> linkPolyL env xs
      )
  ]

updateCounters :: Env -> Counters -> Counters
updateCounters env counters =
  let reducedFX = (WriteField, getCount counters (Intermediate, ReadField) - IntSet.size (envRefFsInEnvF env))
      reducedBX = (WriteBool, getCount counters (Intermediate, ReadBool) - IntSet.size (envRefBsInEnvB env))
      reducedUXs =
        if envUseNewLinker env
          then
            IntMap.mapWithKey
              ( \width table ->
                  let original = getCount counters (Intermediate, ReadUInt width) -- thie is the number of UInt variables used before optimization & linking (regardless of width)
                      current = IntervalTable.size table -- this is the number of bits used after optimization & linking
                   in (WriteUInt width, original - current)
              )
              (envRefBsInEnvUB env)
          else IntMap.mapWithKey (\width set -> (WriteUInt width, getCount counters (Intermediate, ReadUInt width) - IntSet.size set)) (envRefUsInEnvU env)
   in foldr (\(selector, reducedAmount) -> addCount (Intermediate, selector) (-reducedAmount)) counters $ reducedFX : reducedBX : IntMap.elems reducedUXs

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
          (2 ^ i) * if sign then multiplier else (-multiplier)
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
          (2 ^ i) * if sign then multiplier else (-multiplier)
        )
        | (i, sign) <- zip [0 .. lmbWidth limb - 1] signs
      ]

reindexRefF :: Env -> RefF -> Var
reindexRefF env (RefFO x) = x + getOffset (envCounters env) (Output, ReadField)
reindexRefF env (RefFI x) = x + getOffset (envCounters env) (PublicInput, ReadField)
reindexRefF env (RefFP x) = x + getOffset (envCounters env) (PrivateInput, ReadField)
reindexRefF env (RefFX x) = IntervalTable.reindex (envIndexTableF env) x + getOffset (envCounters env) (Intermediate, ReadField)

reindexRefB :: Env -> RefB -> Var
reindexRefB env (RefBO x) = x + getOffset (envCounters env) (Output, ReadBool)
reindexRefB env (RefBI x) = x + getOffset (envCounters env) (PublicInput, ReadBool)
reindexRefB env (RefBP x) = x + getOffset (envCounters env) (PrivateInput, ReadBool)
reindexRefB env (RefBX x) = IntervalTable.reindex (envIndexTableB env) x + getOffset (envCounters env) (Intermediate, ReadBool)
reindexRefB env (RefUBit _ x i) = reindexRefU env x i

reindexRefU :: Env -> RefU -> Int -> Var
reindexRefU env (RefUO w x) i = w * x + (i `mod` w) + getOffset (envCounters env) (Output, ReadAllUInts)
reindexRefU env (RefUI w x) i = w * x + (i `mod` w) + getOffset (envCounters env) (PublicInput, ReadAllUInts)
reindexRefU env (RefUP w x) i = w * x + (i `mod` w) + getOffset (envCounters env) (PrivateInput, ReadAllUInts)
reindexRefU env (RefUX w x) i =
  let result =
        if envUseNewLinker env
          then case IntMap.lookup w (envIndexTableUBWithOffsets env) of
            Nothing -> error "[ panic ] reindexRefU: impossible"
            Just (offset, table) -> IntervalTable.reindex table (w * x + (i `mod` w)) + offset + getOffset (envCounters env) (Intermediate, ReadAllUInts)
          else
            let offset = getOffset (envCounters env) (Intermediate, ReadUInt w) + w * x
             in IntervalTable.reindex (envIndexTable env) (offset - envPinnedSize env) + envPinnedSize env + (i `mod` w)
   in result

-------------------------------------------------------------------------------

-- | Allow us to determine which relations should be extracted from the pool
data Env = Env
  { envCounters :: !Counters,
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
    envUseNewLinker :: !Bool
  }
  deriving (Show)

-- | Smart constructor for 'Env'
constructEnv :: Options -> Counters -> OccurF -> OccurB -> OccurU -> OccurUB -> Env
constructEnv options counters occurF occurB occurU occurUB =
  let tablesUB = OccurUB.toIntervalTables occurUB
   in Env
        { envCounters = counters,
          envRefFsInEnvF = OccurF.occuredSet occurF,
          envRefBsInEnvB = OccurB.occuredSet occurB,
          envRefUsInEnvU = OccurU.occuredSet occurU,
          envRefBsInEnvUB = tablesUB,
          envIndexTableF = OccurF.toIntervalTable counters occurF,
          envIndexTableB = OccurB.toIntervalTable counters occurB,
          envIndexTableUBWithOffsets = OccurUB.toIntervalTablesWithOffsets occurUB,
          envIndexTable =
            OccurF.toIntervalTable counters occurF
              <> OccurB.toIntervalTable counters occurB
              <> OccurU.toIntervalTable counters occurU,
          envPinnedSize = getCount counters Output + getCount counters PublicInput + getCount counters PrivateInput,
          envFieldInfo = optFieldInfo options,
          envFieldWidth = FieldInfo.fieldWidth (optFieldInfo options),
          envUseNewLinker = optUseNewLinker options
        }
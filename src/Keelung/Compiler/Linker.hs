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

import Data.Bifunctor (Bifunctor (first))
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Keelung (GaloisField, HasWidth (widthOf), Var, Width)
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.ConstraintSystem (ConstraintSystem (..))
import Keelung.Compiler.ConstraintSystem qualified as Linked
import Keelung.Compiler.Optimize.OccurB qualified as OccurB
import Keelung.Compiler.Optimize.OccurF qualified as OccurF
import Keelung.Compiler.Optimize.OccurU qualified as OccurU
import Keelung.Compiler.Options
import Keelung.Compiler.Relations qualified as Relations
import Keelung.Compiler.Relations.Reference qualified as RefRelations
import Keelung.Compiler.Relations.Slice qualified as SliceRelations
import Keelung.Data.Constraint
import Keelung.Data.FieldInfo (FieldInfo)
import Keelung.Data.FieldInfo qualified as FieldInfo
import Keelung.Data.IntervalTable (IntervalTable)
import Keelung.Data.IntervalTable qualified as IntervalTable
import Keelung.Data.LC
import Keelung.Data.PolyL
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice (..))
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Syntax.Counters

-------------------------------------------------------------------------------

linkConstraintModule :: (GaloisField n, Integral n) => ConstraintModule n -> ConstraintSystem n
linkConstraintModule cm =
  ConstraintSystem
    { csOptions = cmOptions cm,
      csCounters = envCounters env,
      csConstraints = constraints >>= linkConstraint env,
      csDivMods = fmap (\(a, b, c, d) -> ([a], [b], [c], [d])) divMods,
      csCLDivMods = fmap (\(a, b, c, d) -> ([a], [b], [c], [d])) clDivMods,
      csModInvs = fmap (\(a, b, c, d) -> ([a], [b], [c], d)) modInvs
    }
  where
    !env = constructEnv cm
    -- constraints extracted from the constraint module
    constraints = toConstraints cm env

    -- constraints extracted from hints
    divMods = (\(a, b, q, r) -> (fromEitherRefU a, fromEitherRefU b, fromEitherRefU q, fromEitherRefU r)) <$> cmDivMods cm
    clDivMods = (\(a, b, q, r) -> (fromEitherRefU a, fromEitherRefU b, fromEitherRefU q, fromEitherRefU r)) <$> cmCLDivMods cm
    modInvs = (\(a, output, n, p) -> (fromEitherRefU a, fromEitherRefU output, fromEitherRefU n, toInteger p)) <$> cmModInvs cm

    fromEitherRefU :: Either RefU U -> (Width, Either Var Integer)
    fromEitherRefU (Left var) = let width = widthOf var in (width, Left (reindexRefB env (RefUBit var 0)))
    fromEitherRefU (Right val) = let width = widthOf val in (width, Right (toInteger val))

-------------------------------------------------------------------------------

-- | Predicate on whether a Slice should be exported as constraints
sliceShouldBeKept :: Env -> Slice -> Bool
sliceShouldBeKept env slice = case sliceRefU slice of
  RefUX width var -> case IntMap.lookup width (envOccurU env) of
    Nothing -> False
    Just table -> IntervalTable.member (width * var + sliceStart slice, width * var + sliceEnd slice) table
  _ -> True -- it's a pinned UInt variable

shouldBeKept :: Env -> Ref -> Bool
shouldBeKept env (F ref) = case ref of
  RefFX var ->
    -- it's a Field intermediate variable that occurs in the circuit
    var `IntSet.member` envOccurF env
  _ -> True -- it's a pinned Field variable
shouldBeKept env (B ref) = case ref of
  RefBX var ->
    --  it's a Boolean intermediate variable that occurs in the circuit
    var `IntSet.member` envOccurB env
  RefUBit var i -> refUBitShouldBeKept (envOccurU env) var i
  _ -> True -- it's a pinned Field variable
  where
    refUBitShouldBeKept :: IntMap IntervalTable -> RefU -> Int -> Bool
    refUBitShouldBeKept tables refU i = case refU of
      RefUX width var ->
        case IntMap.lookup width tables of
          Nothing -> False
          Just table -> IntervalTable.member (width * var + i, width * var + i + 1) table
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
linkConstraint env (CSliceEq x y) =
  let x' = reindexSlice env x 1
      y' = reindexSlice env y (-1)
   in case Poly.buildWithIntMap 0 (IntMap.unionWith (+) x' y') of
        Left _ -> error "CSliceEq: impossible"
        Right xs -> Seq.fromList [Linked.CAdd xs]
linkConstraint env (CRefFVal x n) = case Poly.buildEither (-n) [(reindexRef env x, 1)] of
  Left _ -> error "CRefFVal: impossible"
  Right xs -> Seq.fromList [Linked.CAdd xs]
linkConstraint env (CSliceVal slice val) =
  case Poly.buildWithIntMap (fromIntegral val) (reindexSlice env slice (-1)) of
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

updateCounters :: IntervalTable -> IntervalTable -> IntMap (Int, IntervalTable) -> ConstraintModule n -> Counters
updateCounters tableF tableB tableU =
  setCount (Intermediate, WriteField) (IntervalTable.size tableF)
    . setCount (Intermediate, WriteBool) (IntervalTable.size tableB)
    . setCountOfIntermediateUIntBits (fmap (IntervalTable.size . snd) tableU)
    . cmCounters

--------------------------------------------------------------------------------

linkPolyL :: (Integral n, GaloisField n) => Env -> PolyL n -> Either n (Poly n)
linkPolyL env poly =
  let constant = PolyL.polyConstant poly
      slicePolynomial = IntMap.unionsWith (+) (fmap (uncurry (reindexSlice env)) (PolyL.toSlices poly))
      varPolynomial = IntMap.fromList (map (first (reindexRef env)) (Map.toList (PolyL.polyRefs poly)))
   in Poly.buildWithIntMap constant (IntMap.unionWith (+) slicePolynomial varPolynomial)

linkPolyLUnsafe :: (Integral n, GaloisField n) => Env -> PolyL n -> Poly n
linkPolyLUnsafe env xs = case linkPolyL env xs of
  Left _ -> error "[ panic ] linkPolyLUnsafe: Left"
  Right p -> p

--------------------------------------------------------------------------------

reindexRef :: Env -> Ref -> Var
reindexRef env (F x) = reindexRefF env x
reindexRef env (B x) = reindexRefB env x

reindexSlice :: (Integral n, GaloisField n) => Env -> Slice -> n -> IntMap n
reindexSlice env slice multiplier =
  -- precondition of `fromDistinctAscList` is that the keys are in ascending order
  IntMap.fromDistinctAscList
    [ ( reindexRefU
          env
          (Slice.sliceRefU slice)
          (Slice.sliceStart slice + i),
        multiplier * (2 ^ i)
      )
      | i <- [0 .. Slice.sliceEnd slice - Slice.sliceStart slice - 1]
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
reindexRefB env (RefUBit x i) = reindexRefU env x i

reindexRefU :: Env -> RefU -> Int -> Var
reindexRefU env (RefUO w x) i = w * x + i `mod` w + getOffset (envCounters env) (Output, ReadUInt w)
reindexRefU env (RefUI w x) i = w * x + i `mod` w + getOffset (envCounters env) (PublicInput, ReadUInt w)
reindexRefU env (RefUP w x) i = w * x + i `mod` w + getOffset (envCounters env) (PrivateInput, ReadUInt w)
reindexRefU env (RefUX w x) i = case IntMap.lookup w (envIndexTableU env) of
  Nothing -> error "[ panic ] reindexRefU: impossible"
  Just (offset, table) ->
    IntervalTable.reindex table (w * x + i `mod` w) + offset + getOffset (envCounters env) (Intermediate, ReadAllUInts)

-------------------------------------------------------------------------------

-- | Extract Constraints from a ConstraintModule
toConstraints :: (GaloisField n, Integral n) => ConstraintModule n -> Env -> Seq (Constraint n)
toConstraints cm env =
  let -- constraints extracted from relations between Refs
      refConstraints = RefRelations.toConstraints (shouldBeKept env) (Relations.relationsR (cmRelations cm))
      -- constraints extracted from relations between Slices
      sliceConstraints = SliceRelations.toConstraints (envFieldInfo env) (cmOccurrenceU cm) (sliceShouldBeKept env) (Relations.relationsS (cmRelations cm))
      -- constraints extracted from addative constraints
      fromAddativeConstraints = fmap CAddL (cmAddL cm)
      -- constraints extracted from multiplicative constraints
      fromMultiplicativeConstraints =
        fmap
          ( \(a, b, c) ->
              CMulL
                a
                b
                ( case c of
                    Constant n -> Left n
                    Polynomial p -> Right p
                )
          )
          (cmMulL cm)
   in refConstraints
        <> sliceConstraints
        <> fromAddativeConstraints
        <> fromMultiplicativeConstraints

-------------------------------------------------------------------------------

-- | Allow us to determine which relations should be extracted from the pool
data Env = Env
  { envCounters :: !Counters,
    -- for determining which relations should be extracted as constraints
    envOccurF :: !IntSet,
    envOccurB :: !IntSet,
    envOccurU :: !(IntMap IntervalTable),
    -- for variable reindexing
    envIndexTableF :: !IntervalTable,
    envIndexTableB :: !IntervalTable,
    envIndexTableU :: !(IntMap (Int, IntervalTable)),
    -- field related
    envFieldInfo :: !FieldInfo,
    envFieldWidth :: !Width
  }
  deriving (Show)

-- | Smart constructor for 'Env'
constructEnv :: ConstraintModule n -> Env
constructEnv cm =
  let indexTableF = OccurF.toIntervalTable (cmCounters cm) (cmOccurrenceF cm)
      indexTableB = OccurB.toIntervalTable (cmCounters cm) (cmOccurrenceB cm)
      indexTableU = OccurU.toIntervalTablesWithOffsets (cmOccurrenceU cm)
   in Env
        { envCounters = updateCounters indexTableF indexTableB indexTableU cm,
          envOccurF = OccurF.occuredSet (cmOccurrenceF cm),
          envOccurB = OccurB.occuredSet (cmOccurrenceB cm),
          envOccurU = OccurU.toIntervalTables (cmOccurrenceU cm),
          envIndexTableF = indexTableF,
          envIndexTableB = indexTableB,
          envIndexTableU = indexTableU,
          envFieldInfo = optFieldInfo (cmOptions cm),
          envFieldWidth = FieldInfo.fieldWidth (optFieldInfo (cmOptions cm))
        }
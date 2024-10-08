{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Solver.Monad where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Control.Monad.RWS.Strict
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List qualified as List
import Data.Maybe qualified as Maybe
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Serialize (Serialize)
import Data.Validation (toEither)
import Data.Vector (Vector)
import GHC.Generics (Generic)
import Keelung (N (N))
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Compiler.Util
import Keelung.Constraint.R1C
import Keelung.Data.FieldInfo
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Data.UnionFind qualified as UnionFind
import Keelung.Data.UnionFind.Field qualified as Field
import Keelung.Data.VarGroup
import Keelung.Solver.BoolBinomial qualified as BoolBinomial
import Keelung.Syntax
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

-- | Monad for R1CS solving / witness generation
type M n =
  ExceptT
    (Error n)
    ( RWS
        Env
        (Seq (Log n)) -- for debugging
        (Field.UnionFind n) -- variable assignments
    )

runM :: (GaloisField n, Integral n) => Bool -> Ranges -> FieldInfo -> Inputs n -> M n a -> (Either (Error n, Field.UnionFind n) (Vector n), LogReport n)
runM debug boolVarRanges fieldInfo inputs p =
  let counters = Inputs.inputCounters inputs
      -- initial assignments from inputs
      initAssignmints = IntMap.toList $ fmap Field.Wrapper (Inputs.toIntMap inputs)
      initContext = foldr (\(var, val) acc -> Maybe.fromMaybe acc $ Field.assign var val acc) Field.new initAssignmints
      (result, context, logs) = runRWS (runExceptT p) (Env debug boolVarRanges fieldInfo) initContext
      (assignments, _roots) = Field.export context
   in case result of
        Left err -> (Left (err, context), LogReport initContext logs context)
        Right _ -> case toEither $ toTotal' (getCount counters PublicInput + getCount counters PrivateInput, assignments) of
          Left unbound -> (Left (VarUnassignedError unbound, context), LogReport initContext logs context)
          Right bindings' -> (Right bindings', LogReport initContext logs context)

tryLog :: Log n -> M n ()
tryLog x = do
  inDebugMode <- asks envDebugMode
  when inDebugMode $ tell (pure x)

-- | Asssign a value to a variable, with message for debugging
assign :: (GaloisField n, Integral n) => String -> Var -> n -> M n ()
assign msg var val = do
  tryLog $ LogAssign msg var val
  context <- get
  forM_ (Field.assign var (Field.Wrapper val) context) put

-- | Assign a value to a segment (a series of variables)
assignSegment :: (GaloisField n, Integral n) => String -> Segments -> U -> M n ()
assignSegment msg (Segments xs) val = foldM_ bindSegment 0 xs
  where
    bindSegment :: (GaloisField n, Integral n) => Int -> Segment -> M n Int
    bindSegment offset (SegConst x) = return (offset + widthOf x)
    bindSegment offset (SegVar var) = do
      assign msg var (if Data.Bits.testBit val offset then 1 else 0)
      return (offset + 1)
    bindSegment offset (SegVars w var) = do
      forM_ [0 .. w - 1] $ \i -> do
        assign msg (var + i) (if Data.Bits.testBit val (offset + i) then 1 else 0)
      return (offset + w)

-- | Relate a variable to another variable: var1 = slope * var2 + intercept
--   If both var1 and var2 are boolean variables, then we'll try to solve them out right with the BoolBinomial solver
relate ::
  (GaloisField n, Integral n) =>
  String -> -- message for debugging
  Var -> -- var1
  n -> -- slope
  Var -> -- var2
  n -> -- intercept
  M n ()
relate msg var1 slope var2 intercept = do
  context <- get
  var1IsBoolean <- isBooleanVar var1
  var2IsBoolean <- isBooleanVar var2

  let solvedByBoolBinomial =
        if var1IsBoolean && var2IsBoolean
          then BoolBinomial.run (-1) slope intercept
          else Nothing

  case solvedByBoolBinomial of
    Just (val1, val2) -> do
      assign msg var1 (if val1 then 1 else 0)
      assign msg var2 (if val2 then 1 else 0)
    Nothing -> case Field.relate var1 var2 (Field.LinRel slope intercept) context of
      Nothing -> return ()
      Just context' -> do
        tryLog $ LogRelate msg var1 slope var2 intercept
        put context'

-- | See if a variable is a Boolean variable
isBooleanVar :: Var -> M n Bool
isBooleanVar var = do
  boolVarRanges <- asks envBoolVars
  return $ case IntMap.lookupLE var boolVarRanges of
    Nothing -> False
    Just (index, len) -> var < index + len

--------------------------------------------------------------------------------

data Constraint n
  = MulConstraint (Poly n) (Poly n) (Either n (Poly n))
  | AddConstraint (Poly n)
  | BooleanConstraint Var
  | -- | Dividend, Divisor, Quotient, Remainder
    DivModConstaint DivModTuple
  | -- | Dividend, Divisor, Quotient, Remainder
    CLDivModConstaint DivModTuple
  | ModInvConstraint ModInvTuple
  deriving (Eq, Generic, NFData)

instance (Serialize n) => Serialize (Constraint n)

instance (GaloisField n, Integral n) => Show (Constraint n) where
  show (MulConstraint a b (Left c)) = "(" <> show a <> ") * (" <> show b <> ") = " <> show c
  show (MulConstraint a b (Right c)) = "(" <> show a <> ") * (" <> show b <> ") = (" <> show c <> ")"
  show (AddConstraint a) = show a
  show (BooleanConstraint var) = "$" <> show var <> " = $" <> show var <> " * $" <> show var
  show (DivModConstaint (dividend, divisor, quotient, remainder)) =
    "$"
      <> show dividend
      <> " = $"
      <> show divisor
      <> " * $"
      <> show quotient
      <> " + $"
      <> show remainder
  show (CLDivModConstaint (dividend, divisor, quotient, remainder)) =
    "$"
      <> show dividend
      <> " = $"
      <> show divisor
      <> " .*. $"
      <> show quotient
      <> " .^. $"
      <> show remainder
  show (ModInvConstraint (var, _, _, p)) = "$" <> show var <> "⁻¹ (mod " <> show p <> ")"

instance Functor Constraint where
  -- fmap f (R1CConstraint r1c) = R1CConstraint (fmap f r1c)
  fmap f (MulConstraint a b (Left c)) = MulConstraint (fmap f a) (fmap f b) (Left (f c))
  fmap f (MulConstraint a b (Right c)) = MulConstraint (fmap f a) (fmap f b) (Right (fmap f c))
  fmap f (AddConstraint a) = AddConstraint (fmap f a)
  fmap _ (BooleanConstraint var) = BooleanConstraint var
  fmap _ (DivModConstaint (a, b, q, r)) = DivModConstaint (a, b, q, r)
  fmap _ (CLDivModConstaint (a, b, q, r)) = CLDivModConstaint (a, b, q, r)
  fmap _ (ModInvConstraint (a, output, n, p)) = ModInvConstraint (a, output, n, p)

--------------------------------------------------------------------------------

type ModInvTuple = (Segments, Segments, Segments, Integer)

type DivModTuple = (Segments, Segments, Segments, Segments)

toDivModTuple :: (Limbs, Limbs, Limbs, Limbs) -> DivModTuple
toDivModTuple (a, b, c, d) = (limbsToSegments a, limbsToSegments b, limbsToSegments c, limbsToSegments d)

fromDivModTuple :: DivModTuple -> (Limbs, Limbs, Limbs, Limbs)
fromDivModTuple (a, b, c, d) = (segmentsToLimbs a, segmentsToLimbs b, segmentsToLimbs c, segmentsToLimbs d)

--------------------------------------------------------------------------------

type Limbs = [(Width, Either Var Integer)]

-- | For representing either a constant, a single variable, or a series of variables
data Segment
  = SegConst U -- constant
  | SegVar Var -- single variable
  | SegVars Width Var -- series of variables starting from Var
  deriving (Eq, Generic, NFData, Serialize)

instance Show Segment where
  show (SegConst val) = show val <> "[" <> show (widthOf val) <> "]"
  show (SegVar var) = "$" <> show var
  show (SegVars w var) = "$" <> show var <> "..$" <> show (var + w - 1)

instance HasWidth Segment where
  widthOf (SegConst val) = widthOf val
  widthOf (SegVar _) = 1
  widthOf (SegVars w _) = w

newtype Segments = Segments {unSegments :: Seq Segment}
  deriving (Eq, Generic, NFData, Serialize)

instance Show Segments where
  show (Segments xs) = "[ " <> List.intercalate " , " (map show (toList xs)) <> " ]"

instance HasWidth Segments where
  widthOf (Segments xs) = sum (map widthOf (toList xs))

segmentsToLimbs :: Segments -> Limbs
segmentsToLimbs (Segments xs) = map segmentToLimb (toList xs)
  where
    segmentToLimb :: Segment -> (Width, Either Var Integer)
    segmentToLimb (SegConst val) = (widthOf val, Right (toInteger val))
    segmentToLimb (SegVar var) = (1, Left var)
    segmentToLimb (SegVars w var) = (w, Left var)

limbsToSegments :: Limbs -> Segments
limbsToSegments = Segments . Seq.fromList . map limbToSegment
  where
    limbToSegment :: (Width, Either Var Integer) -> Segment
    limbToSegment (w, Right val) = SegConst (U.new w val)
    limbToSegment (1, Left var) = SegVar var
    limbToSegment (w, Left var) = SegVars w var

--------------------------------------------------------------------------------

data Error n
  = VarUnassignedError IntSet
  | R1CInconsistentError (R1C n)
  | ConflictingValues String
  | BooleanConstraintError Var n
  | StuckError (Field.UnionFind n) [Constraint n]
  | ModInvError Segments Integer
  | DividendIsZeroError Segments
  | DivisorIsZeroError Segments
  | QuotientIsZeroError Segments
  deriving (Eq, Generic)

instance (Serialize n) => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (VarUnassignedError unboundVariables) =
    "these variables have no bindings:\n  "
      ++ showList' (map (\var -> "$" <> show var) $ IntSet.toList unboundVariables)
  show (R1CInconsistentError r1c) =
    "equation doesn't hold: `" <> show (fmap N r1c) <> "`"
  show (ConflictingValues msg) = "Cannot unify conflicting values in constraint: " <> msg
  show (BooleanConstraintError var val) =
    "expected the value of $" <> show var <> " to be either 0 or 1, but got `" <> show (N val) <> "`"
  show (StuckError context constraints) =
    let (assignments, roots) = Field.export context
     in "stuck when trying to solve these constraints: \n"
          <> concatMap (\c -> "  " <> show (fmap N c) <> "\n") constraints
          <> "while these variables have been solved: \n"
          <> concatMap (\(var, val) -> "  $" <> show var <> " = " <> show (N val) <> "\n") (IntMap.toList assignments)
          <> ( if IntMap.null roots
                 then ""
                 else "and these equivalence classes have been formed: \n" <> Field.renderFamilies roots
             )
  show (ModInvError segments p) =
    "Unable to calculate '" <> show segments <> " `modInv` " <> show p <> "'"
  show (DividendIsZeroError segments) =
    "Unable to perform division because the bits representing the dividend " <> show segments <> " evaluates to 0"
  show (DivisorIsZeroError segments) =
    "Unable to perform division because the bits representing the divisor " <> show segments <> " evaluates to 0"
  show (QuotientIsZeroError segments) =
    "Unable to perform division because the bits representing the quotient " <> show segments <> " evaluates to 0"

--------------------------------------------------------------------------------

data Env = Env
  { envDebugMode :: Bool, -- enable logging when True
    envBoolVars :: Ranges, -- ranges of boolean variables
    envFieldInfo :: FieldInfo -- information about the field
  }

--------------------------------------------------------------------------------

-- | Data structure for aggregating logging information
data LogReport n = LogReport
  { logReportInitState :: Field.UnionFind n,
    logReportEntries :: Seq (Log n),
    logReportFinalState :: Field.UnionFind n
  }

instance (Integral n, GaloisField n) => Show (LogReport n) where
  show (LogReport initState entries finalState) =
    let (initAssignments, _) = Field.export initState
        (finalAssignments, finalRoots) = Field.export finalState
     in "<Solver Log Report>\n"
          <> "Initial assignments:\n"
          <> concatMap (\(var, val) -> "  $" <> show var <> " = " <> show (N val) <> "\n") (IntMap.toList initAssignments)
          <> "Entries:\n"
          <> concatMap (\entry -> show entry <> "\n") entries
          <> "Final assignments:\n"
          <> concatMap (\(var, val) -> "  $" <> show var <> " = " <> show (N val) <> "\n") (IntMap.toList finalAssignments)
          <> ( if IntMap.null finalRoots
                 then ""
                 else
                   "Final equivalence classes:\n"
                     <> Field.renderFamilies finalRoots
             )

-- | Data structure for log entries
data Log n
  = LogAssign String Var n
  | LogRelate String Var n Var n
  | LogEliminateConstraint (Constraint n)
  | LogShrinkConstraint (Constraint n) (Constraint n)
  | LogBinRepDetection (Poly n) [(Var, Bool)]

data LogEntry
  = LogSimple
      String -- action
      String -- label
      String -- message
  | LogTransition
      String -- action
      String -- label
      String -- before
      String -- after

instance Show LogEntry where
  show (LogSimple action label message) =
    "  " -- left-padding
      <> take 8 (action <> "        ")
      <> "  "
      <> take 8 (label <> "        ")
      <> "  "
      <> message
  show (LogTransition action label before after) =
    "  " -- left-padding
      <> take 8 (action <> "        ")
      <> "  "
      <> take 8 (label <> "        ")
      <> "  "
      <> before
      <> "\n                  ->  "
      <> after

instance (Integral n, GaloisField n) => Show (Log n) where
  show = show . toLogEntry
    where
      toLogEntry (LogAssign msg var val) = LogSimple "assign" msg ("$" <> show var <> " = " <> show (N val))
      toLogEntry (LogRelate msg var1 slope var2 intercept) = LogSimple "relate" msg ("$" <> show var1 <> " = " <> show (N slope) <> " * $" <> show var2 <> " + " <> show (N intercept))
      toLogEntry (LogEliminateConstraint c) = LogSimple "remove" "" (show (fmap N c))
      toLogEntry (LogShrinkConstraint c1 c2) = LogTransition "shrink" "" (show (fmap N c1)) (show (fmap N c2))
      toLogEntry (LogBinRepDetection poly assignments) =
        LogSimple "BinRep" "" (show (fmap N poly) <> "\n" <> concatMap (\(var, val) -> "  -> $" <> show var <> " := " <> show (if val then 1 else 0 :: Int) <> "\n") assignments)

--------------------------------------------------------------------------------

-- | Result of shrinking a constraint
data Result a = Shrinked a | Stuck a | Eliminated | NothingToDo
  deriving (Eq, Show)

instance (Semigroup a) => Semigroup (Result a) where
  NothingToDo <> x = x
  x <> NothingToDo = x
  Shrinked x <> Shrinked y = Shrinked (x <> y)
  Shrinked x <> Stuck y = Shrinked (x <> y)
  Shrinked x <> Eliminated = Shrinked x
  Stuck x <> Shrinked y = Shrinked (x <> y)
  Stuck x <> Stuck y = Stuck (x <> y)
  Stuck x <> Eliminated = Shrinked x
  Eliminated <> Shrinked x = Shrinked x
  Eliminated <> Stuck x = Shrinked x
  Eliminated <> Eliminated = Eliminated

instance (Monoid a) => Monoid (Result a) where
  mempty = NothingToDo

instance Functor Result where
  fmap f (Shrinked x) = Shrinked (f x)
  fmap f (Stuck x) = Stuck (f x)
  fmap _ Eliminated = Eliminated
  fmap _ NothingToDo = NothingToDo

-- | If any of the changes is True, then the result is Shrinked
shrinkedOrStuck :: [Bool] -> a -> Result a
shrinkedOrStuck changes r1c = if or changes then Shrinked r1c else Stuck r1c

-- | Substitute varaibles with values or other variables in a polynomial
substAndView :: (GaloisField n, Integral n) => Field.UnionFind n -> Poly n -> PolyView n
substAndView context xs =
  let (constant, variables, changed) = substPolyHelper context (Poly.view xs)
   in case Poly.buildWithIntMap constant variables of
        Left _ -> Constant constant -- reduced to a constant
        Right afterSubst -> case IntMap.minViewWithKey variables of
          Nothing -> Constant constant -- reduced to a constant
          Just ((var, coeff), vars) ->
            if IntMap.null vars
              then Uninomial changed afterSubst constant (var, coeff)
              else Polynomial changed afterSubst

substPolyHelper :: (GaloisField n, Integral n) => Field.UnionFind n -> (n, IntMap n) -> (n, IntMap n, Bool)
substPolyHelper context (constant, variables) =
  IntMap.foldlWithKey'
    ( \(c, xs, changed) var coeff -> case UnionFind.lookup var context of
        UnionFind.Constant (Field.Wrapper c') -> (c + c' * coeff, xs, True)
        UnionFind.Root _ -> (c, IntMap.insert var coeff xs, changed)
        UnionFind.ChildOf root (Field.LinRel slope intercept) _range ->
          --    child = slope * root + intercept
          -- now that we've learned that the variable to be inserted is a child of a root
          -- before inserting the root, we need to check if it already exists in the polynomial
          case IntMap.lookup root xs of
            Nothing -> (c + intercept * coeff, IntMap.insert root (slope * coeff) xs, True)
            Just coeffOld ->
              if slope * coeff + coeffOld == 0
                then (c + intercept * coeff, IntMap.delete root xs, True) -- root is cancelled out
                else (c + intercept * coeff, IntMap.insert root (slope * coeff + coeffOld) xs, True) -- root is updated
    )
    (constant, mempty, False)
    variables

-- | View of result after substituting a polynomial
data PolyView n
  = Constant n
  | Uninomial -- 0 = c + ax
      Bool -- changed by substitution
      (Poly n) -- polynomial after substitution
      n -- constant term
      (Var, n) -- variable and coefficient
  | Polynomial
      Bool -- changed by substitution
      (Poly n) -- polynomial after substitution
  deriving (Show, Eq, Ord, Functor)

-- | For representing a binomial
data BinomialView n
  = Binomial
      Bool -- changed by substitution
      (Poly n) -- polynomial after substitution
      n -- constant term
      (Var, n) -- variable and coefficient
      (Var, n) -- variable and coefficient
  deriving (Show, Eq, Ord, Functor)

-- | View of a polynomial with more than 1 variable as a binomial
viewBinomial :: (Num n, Eq n) => Bool -> Poly n -> Maybe (BinomialView n)
viewBinomial changed poly = case Poly.view poly of
  (constant, xs) -> case IntMap.toList xs of
    [(var1, coeff1), (var2, coeff2)] -> Just $ Binomial changed poly constant (var1, coeff1) (var2, coeff2)
    _ -> Nothing
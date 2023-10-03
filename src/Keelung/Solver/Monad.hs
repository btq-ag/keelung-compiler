{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Solver.Monad where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Control.Monad.RWS.Strict
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Sequence (Seq)
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
import Keelung.Data.VarGroup
import Keelung.Syntax
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

-- | Monad for R1CS interpretation / witness generation
type M n = ExceptT (Error n) (RWS Env (Seq (Log n)) (IntMap n))

runM :: (GaloisField n, Integral n) => Bool -> Ranges -> FieldInfo -> Inputs n -> M n a -> (Either (Error n, IntMap n) (Vector n), LogReport n)
runM debug boolVarRanges fieldInfo inputs p =
  let counters = Inputs.inputCounters inputs
      initState = Inputs.toIntMap inputs
      (result, bindings, logs) = runRWS (runExceptT p) (Env debug boolVarRanges (fieldWidth fieldInfo)) initState
   in case result of
        Left err -> (Left (err, bindings), LogReport initState logs bindings)
        Right _ -> case toEither $ toTotal' (getCount counters PublicInput + getCount counters PrivateInput, bindings) of
          Left unbound -> (Left (VarUnassignedError unbound, bindings), LogReport initState logs bindings)
          Right bindings' -> (Right bindings', LogReport initState logs bindings)

tryLog :: Log n -> M n ()
tryLog x = do
  inDebugMode <- asks envDebugMode
  when inDebugMode $ tell (pure x)

-- tryLogResult :: (GaloisField n, Integral n) => Constraint n -> Result (Constraint n) -> M n ()
-- tryLogResult before result = do
--   inDebugMode <- asks envDebugMode
--   when inDebugMode $ case result of
--     Shrinked after -> tell (pure $ LogShrinkConstraint before after)
--     Stuck _ -> return ()
--     Eliminated -> tell (pure $ LogEliminateConstraint before)
--     NothingToDo -> return ()

bindVar :: (GaloisField n, Integral n) => String -> Var -> n -> M n ()
bindVar msg var val = do
  tryLog $ LogBindVar msg var val
  modify' $ IntMap.insert var val

bindBitsEither :: (GaloisField n, Integral n) => String -> (Width, Either Var Integer) -> U -> M n ()
bindBitsEither msg (width, Left var) val = do
  forM_ [0 .. width - 1] $ \i -> do
    bindVar msg (var + i) (if Data.Bits.testBit (U.uValue val) i then 1 else 0)
bindBitsEither _ (_, Right _) _ = return ()

--------------------------------------------------------------------------------

data Constraint n
  = MulConstraint (Poly n) (Poly n) (Either n (Poly n))
  | AddConstraint (Poly n)
  | BooleanConstraint Var
  | EqZeroConstraint (Poly n, Var)
  | -- | Dividend, Divisor, Quotient, Remainder
    DivModConstaint ((Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer))
  | CLDivModConstaint ((Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer))
  | ModInvConstraint ((Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer), Integer)
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (Constraint n)

instance (GaloisField n, Integral n) => Show (Constraint n) where
  show (MulConstraint a b (Left c)) = "(Mul)       (" <> show a <> ") * (" <> show b <> ") = (" <> show c <> ")"
  show (MulConstraint a b (Right c)) = "(Mul)       (" <> show a <> ") * (" <> show b <> ") = (" <> show c <> ")"
  show (AddConstraint a) = "(Add)       " <> show a
  show (BooleanConstraint var) = "(Boolean)   $" <> show var <> " = $" <> show var <> " * $" <> show var
  show (EqZeroConstraint eqZero) = "(EqZero)     " <> show eqZero
  show (DivModConstaint (dividend, divisor, quotient, remainder)) =
    "(DivMod)    $"
      <> show dividend
      <> " = $"
      <> show divisor
      <> " * $"
      <> show quotient
      <> " + $"
      <> show remainder
  show (CLDivModConstaint (dividend, divisor, quotient, remainder)) =
    "(CLDivMod)    $"
      <> show dividend
      <> " = $"
      <> show divisor
      <> " .*. $"
      <> show quotient
      <> " .^. $"
      <> show remainder
  show (ModInvConstraint (var, _, _, p)) = "(ModInv)    $" <> show var <> "⁻¹ (mod " <> show p <> ")"

instance Functor Constraint where
  -- fmap f (R1CConstraint r1c) = R1CConstraint (fmap f r1c)
  fmap f (MulConstraint a b (Left c)) = MulConstraint (fmap f a) (fmap f b) (Left (f c))
  fmap f (MulConstraint a b (Right c)) = MulConstraint (fmap f a) (fmap f b) (Right (fmap f c))
  fmap f (AddConstraint a) = AddConstraint (fmap f a)
  fmap _ (BooleanConstraint var) = BooleanConstraint var
  fmap f (EqZeroConstraint (xs, m)) = EqZeroConstraint (fmap f xs, m)
  fmap _ (DivModConstaint (a, b, q, r)) = DivModConstaint (a, b, q, r)
  fmap _ (CLDivModConstaint (a, b, q, r)) = CLDivModConstaint (a, b, q, r)
  fmap _ (ModInvConstraint (a, output, n, p)) = ModInvConstraint (a, output, n, p)

--------------------------------------------------------------------------------

data Error n
  = VarUnassignedError IntSet
  | R1CInconsistentError (R1C n)
  | ConflictingValues
  | BooleanConstraintError Var n
  | StuckError (IntMap n) [Constraint n]
  | ModInvError (Width, Either Var Integer) Integer
  | DividendIsZeroError (Width, Either Var Integer)
  | DivisorIsZeroError (Width, Either Var Integer)
  | QuotientIsZeroError (Width, Either Var Integer)
  deriving (Eq, Generic, NFData, Functor)

instance Serialize n => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (VarUnassignedError unboundVariables) =
    "these variables have no bindings:\n  "
      ++ showList' (map (\var -> "$" <> show var) $ IntSet.toList unboundVariables)
  show (R1CInconsistentError r1c) =
    "equation doesn't hold: `" <> show (fmap N r1c) <> "`"
  -- " <> show (N a) <> " * " <> show (N b) <> " ≠ " <> show (N c) <> "`"
  show ConflictingValues = "Cannot unify conflicting values in constraint"
  -- show (ConflictingValues expected actual) = "Cannot unify conflicting values: " <> show (N expected) <> " and " <> show (N actual)
  show (BooleanConstraintError var val) =
    "expected the value of $" <> show var <> " to be either 0 or 1, but got `" <> show (N val) <> "`"
  show (StuckError context constraints) =
    "stuck when trying to solve these constraints: \n"
      <> concatMap (\c -> "  " <> show (fmap N c) <> "\n") constraints
      <> "while these variables have been solved: \n"
      <> concatMap (\(var, val) -> "  $" <> show var <> " = " <> show (N val) <> "\n") (IntMap.toList context)
  show (ModInvError (_, Left var) p) =
    "Unable to calculate '$" <> show var <> " `modInv` " <> show p <> "'"
  show (ModInvError (_, Right val) p) =
    "Unable to calculate '" <> show val <> " `modInv` " <> show p <> "'"
  show (DividendIsZeroError (width, Left var)) =
    "Unable to perform division because the bits representing the dividend '$" <> show var <> " ~ $" <> show (var + width - 1) <> "' evaluates to 0"
  show (DividendIsZeroError (_, Right _)) =
    "Unable to perform division because the dividend is 0"
  show (DivisorIsZeroError (width, Left var)) =
    "Unable to perform division because the bits representing the divisor '$" <> show var <> " ~ $" <> show (var + width - 1) <> "' evaluates to 0"
  show (DivisorIsZeroError (_, Right _)) =
    "Unable to perform division because the divisor is 0"
  show (QuotientIsZeroError (width, Left var)) =
    "Unable to perform division because the bits representing the quotient '$" <> show var <> " ~ $" <> show (var + width - 1) <> "' evaluates to 0"
  show (QuotientIsZeroError (_, Right _)) =
    "Unable to perform division because the quotient is 0"

--------------------------------------------------------------------------------

data Env = Env
  { envDebugMode :: Bool, -- enable logging when True
    envBoolVars :: Ranges, -- ranges of boolean variables
    envFieldWidth :: Width -- width of the field
  }

--------------------------------------------------------------------------------

-- | Data structure for aggregating logging information
data LogReport n = LogReport
  { logReportInitState :: IntMap n,
    logReportEntries :: Seq (Log n),
    logReportFinalState :: IntMap n
  }

instance (Integral n, GaloisField n) => Show (LogReport n) where
  show (LogReport initState entries finalState) =
    "<Solver Log Report>\n"
      <> "Initial State:\n"
      <> concatMap (\(var, val) -> "  $" <> show var <> " = " <> show (N val) <> "\n") (IntMap.toList initState)
      <> "Entries:\n"
      <> concatMap (\entry -> show entry <> "\n") entries
      <> "Final State:\n"
      <> concatMap (\(var, val) -> "  $" <> show var <> " = " <> show (N val) <> "\n") (IntMap.toList finalState)

-- | Data structure for log entries
data Log n
  = LogBindVar String Var n
  | LogEliminateConstraint (Constraint n)
  | LogShrinkConstraint (Constraint n) (Constraint n)
  | LogBinRepDetection (Poly n) [(Var, Bool)]

instance (Integral n, GaloisField n) => Show (Log n) where
  show (LogBindVar msg var val) = "  BIND  " <> take 10 (msg <> "          ") <> "  $" <> show var <> " := " <> show (N val)
  show (LogEliminateConstraint c) = "  ELIM  " <> show (fmap N c)
  show (LogShrinkConstraint c1 c2) = "  SHNK  " <> show (fmap N c1) <> "\n    ->  " <> show (fmap N c2)
  show (LogBinRepDetection poly assignments) =
    "  BREP  "
      <> show (fmap N poly)
      <> "\n"
      <> concatMap (\(var, val) -> "    ->  $" <> show var <> " := " <> show (if val then 1 else 0 :: Int) <> "\n") assignments

--------------------------------------------------------------------------------

-- | Result of shrinking a constraint
data Result a = Shrinked a | Stuck a | Eliminated | NothingToDo
  deriving (Eq, Show)

instance Semigroup a => Semigroup (Result a) where
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

instance Monoid a => Monoid (Result a) where
  mempty = NothingToDo

instance Functor Result where
  fmap f (Shrinked x) = Shrinked (f x)
  fmap f (Stuck x) = Stuck (f x)
  fmap _ Eliminated = Eliminated
  fmap _ NothingToDo = NothingToDo

-- | If any of the changes is True, then the result is Shrinked
shrinkedOrStuck :: [Bool] -> a -> Result a
shrinkedOrStuck changes r1c = if or changes then Shrinked r1c else Stuck r1c

-- | Substitute varaibles with values in a polynomial
substAndView :: (Num n, Eq n) => IntMap n -> Poly n -> PolyResult n
substAndView bindings xs = case Poly.substWithIntMap xs bindings of
  (Left constant, _) -> Constant constant -- reduced to a constant
  (Right poly, changed) ->
    let (constant, xs') = Poly.view poly
     in case IntMap.minViewWithKey xs' of
          Nothing -> Constant constant -- reduced to a constant
          Just ((var, coeff), xs'') ->
            if IntMap.null xs''
              then Uninomial changed poly constant (var, coeff)
              else Polynomial changed poly

-- | View of result after substituting a polynomial
data PolyResult n
  = Constant n
  | Uninomial Bool (Poly n) n (Var, n)
  | Polynomial Bool (Poly n)
  deriving (Show, Eq, Ord, Functor)

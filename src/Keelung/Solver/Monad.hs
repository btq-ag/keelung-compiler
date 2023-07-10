{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Solver.Monad where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Serialize (Serialize)
import Data.Validation (toEither)
import Data.Vector (Vector)
import GHC.Generics (Generic)
import Keelung (N (N))
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Constraint.R1C
import Keelung.Data.FieldInfo
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.VarGroup
import Keelung.Interpreter.Arithmetics (U)
import Keelung.Interpreter.Arithmetics qualified as U
import Keelung.Syntax
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

-- | Monad for R1CS interpretation / witness generation
type M n = ReaderT (Ranges, Width) (StateT (IntMap n) (Except (Error n)))

runM :: (GaloisField n, Integral n) => Ranges -> FieldInfo -> Inputs n -> M n a -> Either (Error n) (Vector n)
runM boolVarRanges fieldInfo inputs p =
  let counters = Inputs.inputCounters inputs
   in case runExcept (execStateT (runReaderT p (boolVarRanges, fieldWidth fieldInfo)) (Inputs.toIntMap inputs)) of
        Left err -> Left err
        Right bindings -> case toEither $ toTotal' (getCount counters PublicInput + getCount counters PrivateInput, bindings) of
          Left unbound -> Left (VarUnassignedError unbound)
          Right bindings' -> Right bindings'

bindVar :: (GaloisField n, Integral n) => Var -> n -> M n ()
bindVar var val = modify' $ IntMap.insert var val

bindVarEither :: (GaloisField n, Integral n) => Either Var n -> n -> M n ()
bindVarEither (Left var) val = bindVar var val
bindVarEither (Right _) _ = return ()

bindBitsEither :: (GaloisField n, Integral n) => (Width, Either Var Integer) -> U -> M n ()
bindBitsEither (width, Left var) val = do
  forM_ [0 .. width - 1] $ \i -> do
    bindVar (var + i) (if Data.Bits.testBit (U.uintValue val) i then 1 else 0)
bindBitsEither (_, Right _) _ = return ()

--------------------------------------------------------------------------------

data Constraint n
  = MulConstraint (Poly n) (Poly n) (Either n (Poly n))
  | AddConstraint (Poly n)
  | BooleanConstraint Var
  | EqZeroConstraint (Poly n, Var)
  | -- | Dividend, Divisor, Quotient, Remainder
    DivModConstaint ((Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer))
  | -- \| (a, n, p) where modInv a * a = n * p + 1

    -- | BinRepConstraint2 [(Var, Int)]
    ModInvConstraint ((Width, Either Var Integer), (Width, Either Var Integer), (Width, Either Var Integer), Integer)
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (Constraint n)

instance (GaloisField n, Integral n) => Show (Constraint n) where
  show (MulConstraint a b c) = "(Mul)       (" <> show a <> ") * (" <> show b <> ") = (" <> show c <> ")"
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
  -- show (BinRepConstraint2 segments) = "(BinRep)    " <> show segments
  show (ModInvConstraint (var, _, _, p)) = "(ModInv)    $" <> show var <> "⁻¹ (mod " <> show p <> ")"

instance Functor Constraint where
  -- fmap f (R1CConstraint r1c) = R1CConstraint (fmap f r1c)
  fmap f (MulConstraint a b (Left c)) = MulConstraint (fmap f a) (fmap f b) (Left (f c))
  fmap f (MulConstraint a b (Right c)) = MulConstraint (fmap f a) (fmap f b) (Right (fmap f c))
  fmap f (AddConstraint a) = AddConstraint (fmap f a)
  fmap _ (BooleanConstraint var) = BooleanConstraint var
  fmap f (EqZeroConstraint (xs, m)) = EqZeroConstraint (fmap f xs, m)
  fmap _ (DivModConstaint (a, b, q, r)) = DivModConstaint (a, b, q, r)
  fmap _ (ModInvConstraint (a, output, n, p)) = ModInvConstraint (a, output, n, p)

--------------------------------------------------------------------------------

data Error n
  = VarUnassignedError IntSet
  | R1CInconsistentError (R1C n)
  | ConflictingValues
  | BooleanConstraintError Var n
  | StuckError (IntMap n) [Constraint n]
  | ModInvError (Width, Either Var Integer) Integer
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
  -- show (DivModQuotientError dividend divisor expected actual) =
  --   "Expected the result of `" <> show (N dividend) <> " / " <> show (N divisor) <> "` to be `" <> show (N expected) <> "` but got `" <> show (N actual) <> "`"
  -- show (DivModRemainderError dividend divisor expected actual) =
  --   "Expected the result of `" <> show (N dividend) <> " % " <> show (N divisor) <> "` to be `" <> show (N expected) <> "` but got `" <> show (N actual) <> "`"
  show (ModInvError (_, Left var) p) =
    "Unable to calculate '$" <> show var <> " `modInv` " <> show p <> "'"
  show (ModInvError (_, Right val) p) =
    "Unable to calculate '" <> show val <> " `modInv` " <> show p <> "'"
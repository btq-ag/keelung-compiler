{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Interpreter.R1CS.Monad where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Control.Monad.State
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
import Keelung.Data.BinRep (BinRep (..))
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.VarGroup
import Keelung.Syntax
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

-- | Monad for R1CS interpretation / witness generation
type M n = StateT (IntMap n) (Except (Error n))

runM :: (GaloisField n, Integral n) => Inputs n -> M n a -> Either (Error n) (Vector n)
runM inputs p =
  let counters = Inputs.inputCounters inputs
   in case runExcept (execStateT p (Inputs.toIntMap inputs)) of
        Left err -> Left err
        Right bindings -> case toEither $ toTotal' (sum $ getCounts counters [PublicInputField .. PrivateInputUInt], bindings) of
          Left unbound -> Left (VarUnassignedError unbound)
          Right bindings' -> Right bindings'

bindVar :: Var -> n -> M n ()
bindVar var val = modify' $ IntMap.insert var val

bindVarEither :: Either Var n -> n -> M n ()
bindVarEither (Left var) val = bindVar var val
bindVarEither (Right _) _ = return ()

--------------------------------------------------------------------------------

data Constraint n
  = R1CConstraint (R1C n)
  | BooleanConstraint Var
  | EqZeroConstraint (Poly n, Var)
  | -- | Dividend, Divisor, Quotient, Remainder
    DivModConstaint (Either Var n, Either Var n, Either Var n, Either Var n)
  | BinRepConstraint BinRep
  | BinRepConstraint2 [(Var, Int)]
  | -- | (a, n, p) where modInv a * a = n * p + 1
    ModInvConstraint (Either Var n, Either Var n, Integer)
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (Constraint n)

instance (GaloisField n, Integral n) => Show (Constraint n) where
  show (R1CConstraint r1c) = show r1c
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
  show (BinRepConstraint binRep) = "(BinRep)    " <> show binRep
  show (BinRepConstraint2 segments) = "(BinRep)    " <> show segments
  show (ModInvConstraint (var, _, p)) = "(ModInv)    $" <> show var <> "⁻¹ (mod " <> show p <> ")"

instance Functor Constraint where
  fmap f (R1CConstraint r1c) = R1CConstraint (fmap f r1c)
  fmap _ (BooleanConstraint var) = BooleanConstraint var
  fmap f (EqZeroConstraint (xs, m)) = EqZeroConstraint (fmap f xs, m)
  fmap f (DivModConstaint (a, b, q, r)) = DivModConstaint (fmap f a, fmap f b, fmap f q, fmap f r)
  fmap _ (BinRepConstraint binRep) = BinRepConstraint binRep
  fmap _ (BinRepConstraint2 segments) = BinRepConstraint2 segments
  fmap f (ModInvConstraint (a, n, p)) = ModInvConstraint (fmap f a, fmap f n, p)

--------------------------------------------------------------------------------

data Error n
  = VarUnassignedError IntSet
  | R1CInconsistentError (R1C n)
  | BooleanConstraintError Var n
  | StuckError (IntMap n) [Constraint n]
  | DivModQuotientError n n n n
  | DivModRemainderError n n n n
  | ModInvError (Either Var n) n Integer
  deriving (Eq, Generic, NFData, Functor)

instance Serialize n => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (VarUnassignedError unboundVariables) =
    "these variables have no bindings:\n  "
      ++ showList' (map (\var -> "$" <> show var) $ IntSet.toList unboundVariables)
  show (R1CInconsistentError r1c) =
    "equation doesn't hold: `" <> show (fmap N r1c) <> "`"
  -- " <> show (N a) <> " * " <> show (N b) <> " ≠ " <> show (N c) <> "`"
  show (BooleanConstraintError var val) =
    "expected the value of $" <> show var <> " to be either 0 or 1, but got `" <> show (N val) <> "`"
  show (StuckError context constraints) =
    "stuck when trying to solve these constraints: \n"
      <> concatMap (\c -> "  " <> show (fmap N c) <> "\n") constraints
      <> "while these variables have been solved: \n"
      <> concatMap (\(var, val) -> "  $" <> show var <> " = " <> show (N val) <> "\n") (IntMap.toList context)
  show (DivModQuotientError dividend divisor expected actual) =
    "Expected the result of `" <> show (N dividend) <> " / " <> show (N divisor) <> "` to be `" <> show (N expected) <> "` but got `" <> show (N actual) <> "`"
  show (DivModRemainderError dividend divisor expected actual) =
    "Expected the result of `" <> show (N dividend) <> " % " <> show (N divisor) <> "` to be `" <> show (N expected) <> "` but got `" <> show (N actual) <> "`"
  show (ModInvError (Left var) val p) =
    "Unable to calculate the inverse of `$" <> show var <> " " <> show (N val) <> "` (mod " <> show p <> ")"
  show (ModInvError (Right val') val p) =
    "Unable to calculate the inverse of `" <> show (N val') <> " `" <> show (N val) <> "` (mod " <> show p <> ")"
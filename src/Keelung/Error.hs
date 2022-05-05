module Keelung.Error where

import Data.IntMap (IntMap)
import Keelung.R1CS (R1C)
import Keelung.Syntax.Common (Var)
import Keelung.Util (DebugGF (DebugGF))

data Error n
  = ExecError (ExecError n)
  | -- | EraseError EraseError
    OtherError String
  deriving (Eq)

instance (Show n, Bounded n, Integral n, Fractional n) => Show (Error n) where
  show (ExecError e) = "ExecError: " ++ show e
  show (OtherError s) = "OtherError: " ++ s

data ExecError n
  = ExecOutputVarNotMappedError (Maybe Var) (IntMap n)
  | ExecOutputError (Maybe n) (Maybe n)
  | ExecR1CUnsatisfiableError [R1C n] (IntMap n)
  deriving (Eq)

instance (Show n, Bounded n, Integral n, Fractional n) => Show (ExecError n) where
  show (ExecOutputVarNotMappedError var witness) =
    "output variable "
      ++ show var
      ++ " is not mapped in\n  "
      ++ show witness
  show (ExecOutputError expected actual) =
    "interpreted output:\n"
      ++ show (fmap DebugGF expected)
      ++ "\nactual output:\n"
      ++ show (fmap DebugGF actual)
  show (ExecR1CUnsatisfiableError r1c's witness) =
    "these R1C constraints cannot be satisfied:\n"
      ++ show r1c's
      ++ "\nby the witness:\n"
      ++ show (fmap DebugGF witness)
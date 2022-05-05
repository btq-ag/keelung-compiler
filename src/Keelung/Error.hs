module Keelung.Error where

import Keelung.R1CS (ExecError)
import Keelung.Interpret (InterpretError)

data Error n
  = ExecError (ExecError n)
  | InterpretError (InterpretError n)
  | OtherError String
  deriving (Eq)

instance (Show n, Bounded n, Integral n, Fractional n) => Show (Error n) where
  show (ExecError e) = "ExecError: " ++ show e
  show (InterpretError e) = "InterpretError: " ++ show e
  show (OtherError s) = "OtherError: " ++ s

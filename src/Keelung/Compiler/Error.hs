module Keelung.Compiler.Error where

import Keelung.Compiler.R1CS (ExecError)
import Keelung.Compiler.Interpret (InterpretError)
import Keelung.Error (ElabError)

data Error n
  = ExecError (ExecError n)
  | InterpretError (InterpretError n)
  | ElabError ElabError
  deriving (Eq)

instance (Show n, Bounded n, Integral n, Fractional n) => Show (Error n) where
  show (ExecError e) = "Execution Error: " ++ show e
  show (InterpretError e) = "Interpret Error: " ++ show e
  show (ElabError e) = "Elaboration Error: " ++ show e

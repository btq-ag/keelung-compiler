{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.Error where

import Data.Field.Galois (GaloisField)
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Error qualified as Compiler
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Error qualified as Lang
import Keelung.Interpreter.Monad qualified as Interpreter
import Keelung.Solver.Monad qualified as Solver

data Error n
  = InterpreterError (Interpreter.Error n)
  | CompilerError (Compiler.Error n)
  | SolverError (Solver.Error n)
  | InputError Inputs.Error
  | LangError Lang.Error
  deriving (Eq, Generic)

instance (Serialize n) => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (InterpreterError e) = "Interpreter Error: " ++ show e
  show (CompilerError e) = "Compiler Error: " ++ show e
  show (SolverError e) = "Solver Error: " ++ show e
  show (LangError e) = "Language Error: " ++ show e
  show (InputError e) = "Input Error: " ++ show e

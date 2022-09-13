{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.Error where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung.Compiler.Interpret.Typed (InterpretError)
import Keelung.Compiler.R1CS (ExecError)
import Keelung.Error (ElabError)

data Error n
  = ExecError (ExecError n)
  | InterpretError (InterpretError n)
  | ElabError ElabError
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (ExecError e) = "Execution Error: " ++ show e
  show (InterpretError e) = "Interpret Error: " ++ show e
  show (ElabError e) = "Elaboration Error: " ++ show e

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.Error where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung.Compiler.Interpret.Typed (InterpretError)
import Keelung.Compiler.R1CS (ExecError)
import qualified Keelung.Error as Lang

data Error n
  = ExecError (ExecError n)
  | InterpretError (InterpretError n)
  | LangError Lang.Error
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (ExecError e) = "Execution Error: " ++ show e
  show (InterpretError e) = "Interpret Error: " ++ show e
  show (LangError e) = "Language Error: " ++ show e

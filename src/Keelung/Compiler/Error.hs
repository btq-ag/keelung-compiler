{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Keelung.Compiler.Error where

import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung.Compiler.Interpret (InterpretError)
import Keelung.Compiler.R1CS (ExecError)
import Keelung.Error (ElabError)
import Control.DeepSeq (NFData)

data Error n
  = ExecError (ExecError n)
  | InterpretError (InterpretError n)
  | ElabError ElabError
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (Error n)

instance (Show n, Bounded n, Integral n, Fractional n) => Show (Error n) where
  show (ExecError e) = "Execution Error: " ++ show e
  show (InterpretError e) = "Interpret Error: " ++ show e
  show (ElabError e) = "Elaboration Error: " ++ show e

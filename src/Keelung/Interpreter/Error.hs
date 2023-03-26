{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Interpreter.Error where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Interpreter.R1CS qualified as R1CS
import Keelung.Interpreter.SyntaxTree qualified as SyntaxTree

--------------------------------------------------------------------------------

data Error n
  = SyntaxTreeError (SyntaxTree.Error n)
  | R1CSError (R1CS.Error n)
  | InputError Inputs.Error
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (SyntaxTreeError e) = show e
  show (R1CSError e) = show e
  show (InputError e) = show e
module Keelung.Compiler.Compile.Relations.Util (Seniority(..)) where

import Keelung.Compiler.Constraint
import Data.Function (on)

--------------------------------------------------------------------------------

class Seniority a where
  compareSeniority :: a -> a -> Ordering

instance Seniority RefB where
  compareSeniority = compare `on` hasLevel

instance Seniority RefU where
  compareSeniority = compare `on` hasLevel

instance Seniority RefF where
  compareSeniority = compare `on` hasLevel

instance Seniority Ref where
  compareSeniority = compare `on` hasLevel

--------------------------------------------------------------------------------

class HasLevel a where
  hasLevel :: a -> Int 

instance HasLevel RefB where
  hasLevel (RefBX _) = 0
  hasLevel (RefUBit {}) = 99
  hasLevel _ = 100

instance HasLevel RefU where
  hasLevel (RefUX _ _) = 0
  hasLevel _ = 100

instance HasLevel RefF where
  hasLevel (RefFX _) = 0
  hasLevel _ = 100

instance HasLevel Ref where
  hasLevel (F x) = hasLevel x
  hasLevel (B x) = hasLevel x
  hasLevel (U x) = hasLevel x
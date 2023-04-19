module Keelung.Compiler.Compile.Relations.Util where

import Keelung.Compiler.Constraint

--------------------------------------------------------------------------------

class Seniority a where
  compareSeniority :: a -> a -> Ordering

instance Seniority RefB where
  compareSeniority (RefBX _) (RefBX _) = EQ
  compareSeniority (RefBX _) _ = LT
  compareSeniority _ (RefBX _) = GT
  compareSeniority (RefUBit {}) (RefUBit {}) = EQ
  compareSeniority (RefUBit {}) _ = LT
  compareSeniority _ (RefUBit {}) = GT
  compareSeniority _ _ = EQ

instance Seniority RefU where
  compareSeniority (RefUX _ _) (RefUX _ _) = EQ
  compareSeniority (RefUX _ _) _ = LT
  compareSeniority _ (RefUX _ _) = GT
  compareSeniority _ _ = EQ

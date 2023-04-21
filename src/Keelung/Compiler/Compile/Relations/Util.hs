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

instance Seniority RefT where
  compareSeniority (RefFX _) (RefFX _) = EQ
  compareSeniority (RefFX _) _ = LT
  compareSeniority _ (RefFX _) = GT
  compareSeniority _ _ = EQ

instance Seniority Ref where
  compareSeniority (F x) (F y) = compareSeniority x y
  compareSeniority (B x) (B y) = compareSeniority x y
  compareSeniority (U x) (U y) = compareSeniority x y
  compareSeniority _ _ = EQ

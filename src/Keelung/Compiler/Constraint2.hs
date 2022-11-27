{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Keelung.Compiler.Constraint2 where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Set (Set)
import GHC.Generics (Generic)
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Constraint.R1C (R1C (..))
import Keelung.Constraint.R1CS (CNEQ (..))
import Keelung.Field
import Keelung.Syntax.BinRep (BinReps)
import Keelung.Syntax.Counters
import Keelung.Syntax.Typed (Width)
import Keelung.Syntax.VarCounters
import Keelung.Types

--------------------------------------------------------------------------------

data Ref' = RefI Var | RefO Var | Ref Var
  deriving (Generic, NFData, Eq, Ord)

instance Show Ref' where
  show (RefI x) = "$I" ++ show x
  show (RefO x) = "$O" ++ show x
  show (Ref x) = "$" ++ show x

data Type = F | B | U Width | UBit Width Int
  deriving (Generic, NFData, Eq)

data Ref = RefF Ref' | RefB Ref' | RefU Width Ref' | RefUBit Width Ref'

instance Show Type where
  show F = "F"
  show B = "B"
  show (U w) = "U" ++ show w
  show (UBit w i) = "U" ++ show w ++ "[" ++ show i ++ "]"

--------------------------------------------------------------------------------

-- | Constraint
--      CAdd: 0 = c + c₀x₀ + c₁x₁ ... cₙxₙ
--      CMul: ax * by = c or ax * by = cz
--      CNEq: if (x - y) == 0 then m = 0 else m = recip (x - y)
data Constraint n
  = CAdd !(Poly n)
  | CMul !(Poly n) !(Poly n) !(Either n (Poly n))
  | CNEq (CNEQ n) -- x y m
  deriving (Generic, NFData)

instance GaloisField n => Eq (Constraint n) where
  xs == ys = case (xs, ys) of
    (CAdd x, CAdd y) -> x == y
    (CMul x y z, CMul u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    (CNEq x, CNEq y) -> x == y
    _ -> False

instance Functor Constraint where
  fmap f (CAdd x) = CAdd (fmap f x)
  -- fmap f (CAdd2 t x) = CAdd2 t (fmap f x)
  fmap f (CMul x y (Left z)) = CMul (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMul x y (Right z)) = CMul (fmap f x) (fmap f y) (Right (fmap f z))
  fmap f (CNEq x) = CNEq (fmap f x)

-- | Smart constructor for the CAdd constraint
cadd :: GaloisField n => n -> [(Var, n)] -> [Constraint n]
cadd !c !xs = map CAdd $ case Poly.buildEither c xs of
  Left _ -> []
  Right xs' -> [xs']

-- | Smart constructor for the CAdd constraint
cmul :: GaloisField n => [(Var, n)] -> [(Var, n)] -> (n, [(Var, n)]) -> [Constraint n]
cmul !xs !ys (c, zs) = case ( do
                                xs' <- Poly.buildEither 0 xs
                                ys' <- Poly.buildEither 0 ys
                                return $ CMul xs' ys' (Poly.buildEither c zs)
                            ) of
  Left _ -> []
  Right result -> [result]

instance (GaloisField n, Integral n) => Show (Constraint n) where
  show (CAdd xs) = "A " <> show xs <> " = 0"
  -- show (CAdd2 t xs) = "A " <> show t <> " " <> show xs <> " = 0"
  show (CMul aV bV cV) = "M " <> show (R1C (Right aV) (Right bV) cV)
  show (CNEq x) = show x

instance GaloisField n => Ord (Constraint n) where
  {-# SPECIALIZE instance Ord (Constraint GF181) #-}
  -- CMul
  compare (CMul aV bV cV) (CMul aX bX cX) = compare (aV, bV, cV) (aX, bX, cX)
  compare _ CMul {} = LT
  compare CMul {} _ = GT
  -- CAdd
  compare (CAdd xs) (CAdd ys) = compare xs ys
  -- compare (CAdd2 {}) (CAdd {}) = LT
  -- compare (CAdd {}) (CAdd2 {}) = GT
  -- compare (CAdd2 t xs) (CAdd2 u ys) = 
  --   if t == u 
  --     then compare xs ys 
  --     else error "[ panic ] CAdd type mismatch"
  -- CNEq
  compare CNEq {} CNEq {} = EQ
  compare CNEq {} _ = LT
  compare _ CNEq {} = GT

--------------------------------------------------------------------------------

-- | Constraint System
data ConstraintSystem n = ConstraintSystem
  { -- | Constraints
    csConstraints :: !(Set (Constraint n)),
    -- | Binary representation of Number input variables
    csNumBinReps :: BinReps,
    -- | Binary representation of custom output variables
    csCustomBinReps :: BinReps,
    csVarCounters :: !VarCounters,
    csCounters :: Counters
  }
  deriving (Eq, Generic, NFData)
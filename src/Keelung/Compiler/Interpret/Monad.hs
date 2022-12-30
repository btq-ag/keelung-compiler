{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Interpret.Monad where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor (second)
import qualified Data.Bits
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung (N (N))
import Keelung.Compiler.Syntax.Inputs (Inputs)
import qualified Keelung.Compiler.Syntax.Inputs as Inputs
import Keelung.Data.Bindings
import Keelung.Syntax.Counters
import Keelung.Types
import Keelung.Constraint.R1C (R1C)

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = ReaderT (Inputs n) (StateT (Partial n) (Except (Error n)))

runM :: Inputs n -> M n a -> Either (Error n) (a, Witness n)
runM inputs p =
  let counters = Inputs.varCounters inputs
      -- construct the initial partial Bindings from Inputs
      initBindings =
        OIX
          { ofO =
              Struct
                { structF = (getCount OfOutput OfField counters, mempty),
                  structB = (getCount OfOutput OfBoolean counters, mempty),
                  structU = IntMap.mapWithKey (\w _ -> (getCount OfOutput (OfUInt w) counters, mempty)) (Inputs.uintInputs inputs)
                },
            ofI =
              Struct
                { structF = (getCount OfInput OfField counters, IntMap.fromList $ zip [0 ..] (toList (Inputs.numInputs inputs))),
                  structB = (getCount OfInput OfBoolean counters, IntMap.fromList $ zip [0 ..] (toList (Inputs.boolInputs inputs))),
                  structU = IntMap.mapWithKey (\w bindings -> (getCount OfInput (OfUInt w) counters, IntMap.fromList $ zip [0 ..] (toList bindings))) (Inputs.uintInputs inputs)
                },
            ofX =
              Struct
                { structF = (getCount OfIntermediate OfField counters, mempty),
                  structB = (getCount OfIntermediate OfBoolean counters, mempty),
                  structU = IntMap.mapWithKey (\w _ -> (getCount OfIntermediate (OfUInt w) counters, mempty)) (Inputs.uintInputs inputs)
                }
          }
   in do
        (result, partialBindings) <- runExcept (runStateT (runReaderT p inputs) initBindings)
        -- make the partial Bindings total
        case toTotal partialBindings of
          Left unbound -> Left (VarUnassignedError unbound)
          Right bindings -> Right (result, bindings)

addF :: Var -> [n] -> M n ()
addF var vals = modify (updateX (updateF (second (IntMap.insert var (head vals)))))

addB :: Var -> [n] -> M n ()
addB var vals = modify (updateX (updateB (second (IntMap.insert var (head vals)))))

addU :: Width -> Var -> [n] -> M n ()
addU width var vals = modify (updateX (updateU width (second (IntMap.insert var (head vals)))))

lookupVar :: String -> (Partial n -> (Int, IntMap a)) -> Int -> M n a
lookupVar prefix selector var = do
  (_, f) <- gets selector
  case IntMap.lookup var f of
    Nothing -> throwError $ VarUnboundError prefix var
    Just val -> return val

lookupF :: Var -> M n n
lookupF = lookupVar "F" (structF . ofX)

lookupFI :: Var -> M n n
lookupFI = lookupVar "FI" (structF . ofI)

lookupB :: Var -> M n n
lookupB = lookupVar "B" (structB . ofX)

lookupBI :: Var -> M n n
lookupBI = lookupVar "BI" (structB . ofI)

lookupU :: Width -> Var -> M n n
lookupU w = lookupVar ("U" <> toSubscript w) (unsafeLookup w . structU . ofX)

lookupUI :: Width -> Var -> M n n
lookupUI w = lookupVar ("UI" <> toSubscript w) (unsafeLookup w . structU . ofI)

unsafeLookup :: Int -> IntMap a -> a
unsafeLookup x y = case IntMap.lookup x y of
  Nothing -> error "[ panic ] bit width not found"
  Just z -> z

--------------------------------------------------------------------------------

-- | The interpreter typeclass
class Interpret a n where
  interpret :: a -> M n [n]

--------------------------------------------------------------------------------

-- | For collecting free variables
class FreeVar a where
  freeVars :: a -> VarSet n

--------------------------------------------------------------------------------

data Error n
  = VarUnboundError String Var
  | VarUnassignedError (VarSet n)
  | VarUnassignedError' IntSet -- R1CS 
  | AssertionError String (Partial n)
  | AssertionError' String (IntMap n) -- R1CS
  | R1CSStuckError (R1C n) -- R1CS
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (VarUnboundError prefix var) =
    "unbound variable $" <> prefix <> show var
  show (VarUnassignedError unboundVariables) =
    "these variables have no bindings:\n  "
      ++ show unboundVariables
  show (VarUnassignedError' unboundVariables) =
    "these variables have no bindings:\n  "
      ++ showList' (map (\var -> "$" <> show var) $ IntSet.toList unboundVariables)
  show (AssertionError expr bindings) =
    "assertion failed: " <> expr
      <> "\nbindings of free variables in the assertion:\n"
      <> show bindings
  show (AssertionError' expr bindings) =
    "assertion failed: " <> expr
      <> "\nbindings of free variables in the assertion:\n"
      <> showList' (map (\(var, val) -> "$" <> show var <> " = " <> show (N val)) (IntMap.toList bindings))
  show (R1CSStuckError r1c) = 
    "stuck at " <> show r1c

--------------------------------------------------------------------------------

bitWiseAnd :: (GaloisField n, Integral n) => n -> n -> n
bitWiseAnd x y = fromInteger $ (Data.Bits..&.) (toInteger x) (toInteger y)

bitWiseOr :: (GaloisField n, Integral n) => n -> n -> n
bitWiseOr x y = fromInteger $ (Data.Bits..|.) (toInteger x) (toInteger y)

bitWiseXor :: (GaloisField n, Integral n) => n -> n -> n
bitWiseXor x y = fromInteger $ Data.Bits.xor (toInteger x) (toInteger y)

bitWiseNot :: (GaloisField n, Integral n) => n -> n
bitWiseNot x = fromInteger $ Data.Bits.complement (toInteger x)

-- w is the bit width of the result
-- n is the amount to shift left by
-- x is the value to shift
bitWiseRotateL :: (GaloisField n, Integral n) => Width -> Int -> n -> n
bitWiseRotateL w n x =
  fromInteger $
    (toInteger x `Data.Bits.shiftL` fromIntegral (n `mod` w) Data.Bits..&. (2 ^ w - 1))
      Data.Bits..|. (toInteger x `Data.Bits.shiftR` fromIntegral (w - (n `mod` w)))

bitWiseShiftL :: (GaloisField n, Integral n) => Width -> Int -> n -> n
bitWiseShiftL w n x =
  if n < 0
    then fromInteger $ Data.Bits.shiftR (toInteger x) (-n)
    else fromInteger $ Data.Bits.shiftL (toInteger x) n Data.Bits..&. (2 ^ w - 1)
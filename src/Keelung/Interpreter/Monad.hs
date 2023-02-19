{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Interpreter.Monad where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor (second)
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung (N (N))
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Constraint.R1C (R1C)
import Keelung.Constraint.R1CS (CNEQ)
import Keelung.Data.BinRep (BinRep)
import Keelung.Data.Witness
import Keelung.Heap
import Keelung.Syntax
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

data Constraint n
  = R1CConstraint (R1C n)
  | CNEQConstraint (CNEQ n)
  | BinRepConstraint BinRep
  deriving (Eq, Show, Generic, NFData)

instance Serialize n => Serialize (Constraint n)

instance Functor Constraint where
  fmap f (R1CConstraint r1c) = R1CConstraint (fmap f r1c)
  fmap f (CNEQConstraint cneq) = CNEQConstraint (fmap f cneq)
  fmap _ (BinRepConstraint binRep) = BinRepConstraint binRep

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = ReaderT Heap (StateT (Partial n) (Except (Error n)))

runM :: (GaloisField n, Integral n) => Heap -> Inputs n -> M n a -> Either (Error n) (a, Witness n)
runM heap inputs p = do
  partialBindings <- toPartialBindings inputs
  (result, partialBindings') <- runExcept (runStateT (runReaderT p heap) partialBindings)
  -- make the partial Bindings total
  case toTotal partialBindings' of
    Left unbound -> Left (VarUnassignedError unbound)
    Right bindings -> Right (result, bindings)

-- | Construct partial Bindings from Inputs
toPartialBindings :: (GaloisField n, Integral n) => Inputs n -> Either (Error n) (Partial n)
toPartialBindings inputs =
  let counters = Inputs.inputCounters inputs
      expectedInputSize = getCountBySort OfPublicInput counters + getCountBySort OfPrivateInput counters
      actualInputSize = Inputs.size inputs
   in if expectedInputSize /= actualInputSize
        then Left (InputSizeError (Inputs.size inputs) expectedInputSize)
        else
          Right $
            Rows
              { ofO =
                  HStruct
                    (getCount OfOutput OfField counters, mempty)
                    (getCount OfOutput OfBoolean counters, mempty)
                    (IntMap.mapWithKey (\w _ -> (getCount OfOutput (OfUInt w) counters, mempty)) (Inputs.seqUInt (Inputs.inputPublic inputs))),
                ofI =
                  HStruct
                    (getCount OfPublicInput OfField counters, IntMap.fromList $ zip [0 ..] (toList (Inputs.seqField (Inputs.inputPublic inputs))))
                    (getCount OfPublicInput OfBoolean counters, IntMap.fromList $ zip [0 ..] (toList (Inputs.seqBool (Inputs.inputPublic inputs))))
                    (IntMap.mapWithKey (\w bindings -> (getCount OfPublicInput (OfUInt w) counters, IntMap.fromList $ zip [0 ..] (toList bindings))) (Inputs.seqUInt (Inputs.inputPublic inputs))),
                ofP =
                  HStruct
                    (getCount OfPrivateInput OfField counters, IntMap.fromList $ zip [0 ..] (toList (Inputs.seqField (Inputs.inputPrivate inputs))))
                    (getCount OfPrivateInput OfBoolean counters, IntMap.fromList $ zip [0 ..] (toList (Inputs.seqBool (Inputs.inputPrivate inputs))))
                    (IntMap.mapWithKey (\w bindings -> (getCount OfPrivateInput (OfUInt w) counters, IntMap.fromList $ zip [0 ..] (toList bindings))) (Inputs.seqUInt (Inputs.inputPrivate inputs))),
                ofX =
                  HStruct
                    (getCount OfIntermediate OfField counters, mempty)
                    (getCount OfIntermediate OfBoolean counters, mempty)
                    (IntMap.mapWithKey (\w _ -> (getCount OfIntermediate (OfUInt w) counters, mempty)) (Inputs.seqUInt (Inputs.inputPublic inputs)))
              }

addF :: Var -> [n] -> M n ()
addF var vals = modify (updateX (modifyF (second (IntMap.insert var (head vals)))))

addB :: Var -> [n] -> M n ()
addB var vals = modify (updateX (modifyB (second (IntMap.insert var (head vals)))))

addU :: Width -> Var -> [n] -> M n ()
addU width var vals = modify (updateX (modifyU width (second (IntMap.insert var (head vals)))))

lookupVar :: (GaloisField n, Integral n) => String -> (Partial n -> (Int, IntMap n)) -> Int -> M n n
lookupVar prefix selector var = do
  (_, f) <- gets selector
  case IntMap.lookup var f of
    Nothing -> throwError $ VarUnboundError prefix var
    Just val -> return val

lookupF :: (GaloisField n, Integral n) => Var -> M n n
lookupF = lookupVar "F" (getF . ofX)

lookupFI :: (GaloisField n, Integral n) => Var -> M n n
lookupFI = lookupVar "FI" (getF . ofI)

lookupFP :: (GaloisField n, Integral n) => Var -> M n n
lookupFP = lookupVar "FP" (getF . ofP)

lookupB :: (GaloisField n, Integral n) => Var -> M n n
lookupB = lookupVar "B" (getB . ofX)

lookupBI :: (GaloisField n, Integral n) => Var -> M n n
lookupBI = lookupVar "BI" (getB . ofI)

lookupBP :: (GaloisField n, Integral n) => Var -> M n n
lookupBP = lookupVar "BP" (getB . ofP)

lookupU :: (GaloisField n, Integral n) => Width -> Var -> M n n
lookupU w = lookupVar ("U" <> toSubscript w) (unsafeLookup . getU w . ofX)

lookupUI :: (GaloisField n, Integral n) => Width -> Var -> M n n
lookupUI w = lookupVar ("UI" <> toSubscript w) (unsafeLookup . getU w . ofI)

lookupUP :: (GaloisField n, Integral n) => Width -> Var -> M n n
lookupUP w = lookupVar ("UP" <> toSubscript w) (unsafeLookup . getU w . ofP)

-- | TODO: remove this
unsafeLookup :: Maybe a -> a
unsafeLookup Nothing = error "[ panic ] bit width not found"
unsafeLookup (Just x) = x

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
  | R1CSStuckError [Constraint n] -- R1CS
  | InputSizeError Int Int
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (VarUnboundError prefix var) =
    "unbound variable " <> prefix <> show var
  show (VarUnassignedError unboundVariables) =
    "these variables have no bindings:\n  "
      ++ show unboundVariables
  show (VarUnassignedError' unboundVariables) =
    "these variables have no bindings:\n  "
      ++ showList' (map (\var -> "$" <> show var) $ IntSet.toList unboundVariables)
  show (AssertionError expr bindings) =
    "assertion failed: "
      <> expr
      <> "\nbindings of free variables in the assertion:\n"
      <> show bindings
  show (AssertionError' expr bindings) =
    "assertion failed: "
      <> expr
      <> "\nbindings of free variables in the assertion:\n"
      <> showList' (map (\(var, val) -> "$" <> show var <> " = " <> show (N val)) (IntMap.toList bindings))
  show (R1CSStuckError constraint) =
    "stuck at " <> show constraint
  show (InputSizeError expected actual) =
    "expecting " <> show expected <> " input(s) but got " <> show actual <> " input(s)"

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

bitWiseSet :: (GaloisField n, Integral n) => Width -> n -> Int -> n -> n
bitWiseSet w x i b =
  let i' = i `mod` w
   in case toInteger b of
        0 -> fromInteger $ Data.Bits.clearBit (toInteger x) i'
        _ -> fromInteger $ Data.Bits.setBit (toInteger x) i'
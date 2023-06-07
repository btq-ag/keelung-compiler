{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Interpreter.SyntaxTree.Monad where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor (second)
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Data.Struct (Struct (..))
import Keelung.Data.VarGroup
import Keelung.Data.VarGroup qualified as VarGroup
import Keelung.Heap
import Keelung.Syntax
import Keelung.Syntax.Counters
import Keelung.Interpreter.Arithmetics (U (..))

--------------------------------------------------------------------------------

toBool :: (GaloisField n, Integral n) => n -> Bool
toBool = (/= 0)

-- | The interpreter monad
type M n = ReaderT Heap (StateT (Partial n) (Except (Error n)))

runM :: (GaloisField n, Integral n) => Heap -> Inputs n -> M n [n] -> Either (Error n) ([Integer], VarGroup.Witness Integer Integer Integer)
runM heap inputs p = do
  partialBindings <- toPartialBindings inputs
  (result, partialBindings') <- runExcept (runStateT (runReaderT p heap) partialBindings)
  -- make the partial Bindings total
  case toTotal partialBindings' of
    Left unbound -> Left (VarUnassignedError unbound)
    Right bindings -> Right (map toInteger result, convertWitness bindings)

-- | Construct partial Bindings from Inputs
toPartialBindings :: (GaloisField n, Integral n) => Inputs n -> Either (Error n) (Partial n)
toPartialBindings inputs =
  let counters = Inputs.inputCounters inputs
   in Right $
        VarGroups
          { ofO =
              Struct
                (getCount counters (Output, ReadField), mempty)
                (getCount counters (Output, ReadBool), mempty)
                (IntMap.mapWithKey (\w _ -> (getCount counters (Output, ReadUInt w), mempty)) (Inputs.seqUInt (Inputs.inputPublic inputs))),
            ofI =
              Struct
                (getCount counters (PublicInput, ReadField), IntMap.fromList $ zip [0 ..] (toList (Inputs.seqField (Inputs.inputPublic inputs))))
                (getCount counters (PublicInput, ReadBool), IntMap.fromList $ zip [0 ..] (toList (fmap toBool (Inputs.seqBool (Inputs.inputPublic inputs)))))
                (IntMap.mapWithKey (\w bindings -> (getCount counters (PublicInput, ReadUInt w), IntMap.fromList $ zip [0 ..] (map (UVal w) (toList bindings)))) (Inputs.seqUInt (Inputs.inputPublic inputs))),
            ofP =
              Struct
                (getCount counters (PrivateInput, ReadField), IntMap.fromList $ zip [0 ..] (toList (Inputs.seqField (Inputs.inputPrivate inputs))))
                (getCount counters (PrivateInput, ReadBool), IntMap.fromList $ zip [0 ..] (toList (fmap toBool (Inputs.seqBool (Inputs.inputPrivate inputs)))))
                (IntMap.mapWithKey (\w bindings -> (getCount counters (PrivateInput, ReadUInt w), IntMap.fromList $ zip [0 ..] (map (UVal w) (toList bindings)))) (Inputs.seqUInt (Inputs.inputPrivate inputs))),
            ofX =
              Struct
                (getCount counters (Intermediate, ReadField), mempty)
                (getCount counters (Intermediate, ReadBool), mempty)
                (IntMap.mapWithKey (\w _ -> (getCount counters (Intermediate, ReadUInt w), mempty)) (Inputs.seqUInt (Inputs.inputPublic inputs)))
          }

addF :: Var -> [n] -> M n ()
addF var vals = modify (modifyX (modifyF (second (IntMap.insert var (head vals)))))

addB :: Var -> [Bool] -> M n ()
addB var vals = modify (modifyX (modifyB (second (IntMap.insert var (head vals)))))

addU :: Width -> Var -> [U] -> M n ()
addU width var vals = modify (modifyX (modifyU width (0, mempty) (second (IntMap.insert var (head vals)))))

lookupVar :: (GaloisField n, Integral n) => String -> (Partial n -> (Int, IntMap n)) -> Int -> M n n
lookupVar prefix selector var = do
  (_, f) <- gets selector
  case IntMap.lookup var f of
    Nothing -> throwError $ VarUnboundError prefix var
    Just val -> return val

lookupVarB :: (GaloisField n, Integral n) => String -> (Partial n -> (Int, IntMap Bool)) -> Int -> M n Bool
lookupVarB prefix selector var = do
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

lookupB :: (GaloisField n, Integral n) => Var -> M n Bool
lookupB = lookupVarB "B" (getB . ofX)

lookupBI :: (GaloisField n, Integral n) => Var -> M n Bool
lookupBI = lookupVarB "BI" (getB . ofI)

lookupBP :: (GaloisField n, Integral n) => Var -> M n Bool
lookupBP = lookupVarB "BP" (getB . ofP)

lookupVarU :: (GaloisField n, Integral n) => String -> (VarGroups (Struct (PartialBinding n) (PartialBinding Bool) (PartialBinding U)) -> Struct (PartialBinding n) (PartialBinding Bool) (PartialBinding U)) -> Width -> Var -> M n U
lookupVarU prefix selector w var = do
  gets (getU w . selector) >>= \case
    Nothing -> throwError $ VarUnboundError prefix var
    Just (_, f) -> do
      case IntMap.lookup var f of
        Nothing -> throwError $ VarUnboundError prefix var
        Just val -> return val

lookupU :: (GaloisField n, Integral n) => Width -> Var -> M n U
lookupU w = lookupVarU ("U" <> toSubscript w) ofX w

lookupUI :: (GaloisField n, Integral n) => Width -> Var -> M n U
lookupUI w = lookupVarU ("UI" <> toSubscript w) ofI w

lookupUP :: (GaloisField n, Integral n) => Width -> Var -> M n U
lookupUP w = lookupVarU ("UP" <> toSubscript w) ofP w

-- | TODO: remove this
unsafeLookup :: Maybe a -> a
unsafeLookup Nothing = error "[ panic ] bit width not found"
unsafeLookup (Just x) = x

--------------------------------------------------------------------------------

-- | The interpreter typeclass
class Interpret a n where
  interpret :: a -> M n [n]

class InterpretB a n where
  interpretB :: a -> M n [Bool]

class InterpretU a n where
  interpretU :: a -> M n [U]


--------------------------------------------------------------------------------

-- | For collecting free variables
class FreeVar a where
  freeVars :: a -> VarSet n

--------------------------------------------------------------------------------

data Error n
  = VarUnboundError String Var
  | VarUnassignedError (VarSet n)
  | ResultSizeError Int Int
  | AssertionError String
  | DivModQuotientError Integer Integer Integer Integer
  | DivModRemainderError Integer Integer Integer Integer
  | DivModStuckError [Var]
  | AssertLTEError Integer Integer
  | AssertLTEBoundTooSmallError Integer
  | AssertLTEBoundTooLargeError Integer Width
  | AssertLTError Integer Integer
  | AssertLTBoundTooSmallError Integer
  | AssertLTBoundTooLargeError Integer Width
  | AssertGTEError Integer Integer
  | AssertGTEBoundTooSmallError Integer
  | AssertGTEBoundTooLargeError Integer Width
  | AssertGTError Integer Integer
  | AssertGTBoundTooSmallError Integer
  | AssertGTBoundTooLargeError Integer Width
  | ModInvError Integer Integer
  deriving (Eq, Generic, NFData, Functor)

instance Serialize n => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (VarUnboundError prefix var) =
    "unbound variable " <> prefix <> show var
  show (VarUnassignedError unboundVariables) =
    "these variables have no bindings:\n  "
      ++ show unboundVariables
  show (ResultSizeError expected actual) =
    "expecting " <> show expected <> " result(s) but got " <> show actual <> " result(s)"
  show (AssertionError expr) =
    "assertion failed: " <> expr
  show (DivModQuotientError dividend divisor expected actual) =
    "expected the result of `" <> show dividend <> " / " <> show divisor <> "` to be `" <> show expected <> "` but got `" <> show actual <> "`"
  show (DivModRemainderError dividend divisor expected actual) =
    "expected the result of `" <> show dividend <> " % " <> show divisor <> "` to be `" <> show expected <> "` but got `" <> show actual <> "`"
  show (DivModStuckError msg) =
    "stuck when trying to perform Div/Mod operation because the value of these variables "
      <> show msg
      <> " are not known "
  show (AssertLTEError actual bound) =
    "`" <> show actual <> "` is not less than or equal to `" <> show bound <> "`"
  show (AssertLTEBoundTooSmallError bound) = "assertLTE: the bound `" <> show bound <> "` is too restrictive, no UInt can be less than or equal to it"
  show (AssertLTEBoundTooLargeError bound width) =
    "assertLTE: the bound `"
      <> show bound
      <> "` is too large, since all UInt of bit width `"
      <> show width
      <> "` are less than`"
      <> show ((2 ^ width) :: Integer)
      <> "`"
  show (AssertLTError actual bound) =
    "`" <> show actual <> "` is not less than `" <> show bound <> "`"
  show (AssertLTBoundTooSmallError bound) = "assertLT: the bound `" <> show bound <> "` is too restrictive, no UInt can be less than it"
  show (AssertLTBoundTooLargeError bound width) =
    "assertLT: the bound `"
      <> show bound
      <> "` is too large, since all UInt of bit width `"
      <> show width
      <> "` are less than `"
      <> show ((2 ^ width) :: Integer)
      <> "`"
  show (AssertGTEError actual bound) =
    "`" <> show actual <> "` is not greater than or equal to `" <> show bound <> "`"
  show (AssertGTEBoundTooSmallError bound) = "assertGTE: the bound `" <> show bound <> "` is too small, all UInt are greater than or equal to it"
  show (AssertGTEBoundTooLargeError bound width) =
    "assertGTE: the bound `"
      <> show bound
      <> "` is too restrictive, since all UInt of bit width `"
      <> show width
      <> "` are less than `"
      <> show ((2 ^ width) :: Integer)
      <> "`"
  show (AssertGTError actual bound) =
    "`" <> show actual <> "` is not greater than `" <> show bound <> "`"
  show (AssertGTBoundTooSmallError bound) = "assertGT: the bound `" <> show bound <> "` is too small, all UInt are greater than it"
  show (AssertGTBoundTooLargeError bound width) =
    "assertGT: the bound `"
      <> show bound
      <> "` is too restrictive, since all UInt of bit width `"
      <> show width
      <> "` are less than `"
      <> show ((2 ^ width) :: Integer)
      <> "`"
  show (ModInvError a m) =
    "no modular inverse of `" <> show a <> " (mod " <> show m <> ")`"
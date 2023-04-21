{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
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
import Keelung (N (N))
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Data.VarGroup
import Keelung.Data.VarGroup qualified as VarGroup
import Keelung.Heap
import Keelung.Syntax
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = ReaderT Heap (StateT (Partial n) (Except (Error n)))

runM :: (GaloisField n, Integral n) => Heap -> Inputs n -> M n a -> Either (Error n) (a, VarGroup.Witness n)
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
   in -- expectedInputSize = getCountBySort OfPublicInput counters + getCountBySort OfPrivateInput counters
      -- actualInputSize = Inputs.size inputs

      Right $
        VarGroups
          { ofO =
              VarGroup
                (getCount OfOutput OfField counters, mempty)
                (getCount OfOutput OfBoolean counters, mempty)
                (IntMap.mapWithKey (\w _ -> (getCount OfOutput (OfUInt w) counters, mempty)) (Inputs.seqUInt (Inputs.inputPublic inputs))),
            ofI =
              VarGroup
                (getCount OfPublicInput OfField counters, IntMap.fromList $ zip [0 ..] (toList (Inputs.seqField (Inputs.inputPublic inputs))))
                (getCount OfPublicInput OfBoolean counters, IntMap.fromList $ zip [0 ..] (toList (Inputs.seqBool (Inputs.inputPublic inputs))))
                (IntMap.mapWithKey (\w bindings -> (getCount OfPublicInput (OfUInt w) counters, IntMap.fromList $ zip [0 ..] (toList bindings))) (Inputs.seqUInt (Inputs.inputPublic inputs))),
            ofP =
              VarGroup
                (getCount OfPrivateInput OfField counters, IntMap.fromList $ zip [0 ..] (toList (Inputs.seqField (Inputs.inputPrivate inputs))))
                (getCount OfPrivateInput OfBoolean counters, IntMap.fromList $ zip [0 ..] (toList (Inputs.seqBool (Inputs.inputPrivate inputs))))
                (IntMap.mapWithKey (\w bindings -> (getCount OfPrivateInput (OfUInt w) counters, IntMap.fromList $ zip [0 ..] (toList bindings))) (Inputs.seqUInt (Inputs.inputPrivate inputs))),
            ofX =
              VarGroup
                (getCount OfIntermediate OfField counters, mempty)
                (getCount OfIntermediate OfBoolean counters, mempty)
                (IntMap.mapWithKey (\w _ -> (getCount OfIntermediate (OfUInt w) counters, mempty)) (Inputs.seqUInt (Inputs.inputPublic inputs)))
          }

addF :: Var -> [n] -> M n ()
addF var vals = modify (modifyX (modifyF (second (IntMap.insert var (head vals)))))

addB :: Var -> [n] -> M n ()
addB var vals = modify (modifyX (modifyB (second (IntMap.insert var (head vals)))))

addU :: Width -> Var -> [n] -> M n ()
addU width var vals = modify (modifyX (modifyU width (0, mempty) (second (IntMap.insert var (head vals)))))

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

lookupVarU :: (GaloisField n, Integral n) => String -> (VarGroups (VarGroup (PartialBinding n)) -> VarGroup (PartialBinding n)) -> Width -> Var -> M n n
lookupVarU prefix selector w var = do
  gets (getU w . selector) >>= \case
    Nothing -> throwError $ VarUnboundError prefix var
    Just (_, f) -> do
      case IntMap.lookup var f of
        Nothing -> throwError $ VarUnboundError prefix var
        Just val -> return val

lookupU :: (GaloisField n, Integral n) => Width -> Var -> M n n
lookupU w = lookupVarU ("U" <> toSubscript w) ofX w

lookupUI :: (GaloisField n, Integral n) => Width -> Var -> M n n
lookupUI w = lookupVarU ("UI" <> toSubscript w) ofI w

lookupUP :: (GaloisField n, Integral n) => Width -> Var -> M n n
lookupUP w = lookupVarU ("UP" <> toSubscript w) ofP w

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
  | ResultSizeError Int Int
  | AssertionError String
  | DivModQuotientError n n n n
  | DivModRemainderError n n n n
  | DivModStuckError [Var]
  | AssertLTEError n Integer
  | AssertLTError n Integer
  | AssertGTEError n Integer
  | AssertGTError n Integer
  | ModInvError Integer Integer
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (Error n)

instance (GaloisField n, Integral n) => Show (Error n) where
  show (VarUnboundError prefix var) =
    "unbound variable " <> prefix <> show var
  show (VarUnassignedError unboundVariables) =
    "these variables have no bindings:\n  "
      ++ show unboundVariables
  show (ResultSizeError expected actual) =
    "expecting " <> show expected <> " result(s) but got " <> show actual <> " result(s)"
  -- show (StuckError msg vars) =
  --   "stuck because the value of these variables "
  --     <> showList' (map (\x -> "$" <> show x) vars)
  --     <> " are not known "
  --     <> msg
  show (AssertionError expr) =
    "assertion failed: " <> expr
  show (DivModQuotientError dividend divisor expected actual) =
    "expected the result of `" <> show (N dividend) <> " / " <> show (N divisor) <> "` to be `" <> show (N expected) <> "` but got `" <> show (N actual) <> "`"
  show (DivModRemainderError dividend divisor expected actual) =
    "expected the result of `" <> show (N dividend) <> " % " <> show (N divisor) <> "` to be `" <> show (N expected) <> "` but got `" <> show (N actual) <> "`"
  show (DivModStuckError msg) =
    "stuck when trying to perform Div/Mod operation because the value of these variables "
      <> show msg
      <> " are not known "
  show (AssertLTEError actual bound) =
    "`" <> show (N actual) <> "` is not lesser than or equal to `" <> show bound <> "`"
  show (AssertLTError actual bound) =
    "`" <> show (N actual) <> "` is not lesser than `" <> show bound <> "`"
  show (AssertGTEError actual bound) =
    "`" <> show (N actual) <> "` is not greater than or equal to `" <> show bound <> "`"
  show (AssertGTError actual bound) =
    "`" <> show (N actual) <> "` is not greater than `" <> show bound <> "`"
  show (ModInvError a m) =
    "no modular inverse of `" <> show a <> " (mod " <> show m <> ")`"
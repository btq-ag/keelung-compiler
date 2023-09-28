-- Interpreter for Keelung.Syntax.Encode.Syntax
{-# LANGUAGE FlexibleInstances #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Interpreter (runAndOutputWitnesses, run, interpretDivMod, Error (..)) where

import Control.Monad.Except
import Data.Bits (Bits (..))
import Data.Either qualified as Either
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntSet qualified as IntSet
import Data.Semiring (Semiring (..))
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Data.U qualified as U
import Keelung.Data.VarGroup
import Keelung.Interpreter.Monad
import Keelung.Syntax (Var, Width)
import Keelung.Syntax.Encode.Syntax
import Keelung.Data.U (U)

--------------------------------------------------------------------------------

-- | Interpret a program with inputs and return outputs along with the witness
runAndOutputWitnesses :: (GaloisField n, Integral n) => Elaborated -> Inputs n -> Either (Error n) ([Integer], Witness Integer Integer Integer)
runAndOutputWitnesses (Elaborated expr comp) inputs = runM mempty inputs $ do
  -- interpret side-effects
  forM_ (compSideEffects comp) $ \sideEffect -> void $ interpret sideEffect

  -- interpret the assertions next
  -- throw error if any assertion fails
  forM_ (compAssertions comp) $ \e -> do
    values <- interpretExpr e
    when (values /= [1]) $ do
      -- bindings <- get
      -- let bindingsInExpr = Bindings.restrictVars bindings (freeVars e)
      -- collect variables and their bindings in the expression and report them
      throwError $ AssertionError (show e)
  -- lastly interpret the expression and return the result
  interpretExpr expr

-- | Interpret a program with inputs.
run :: (GaloisField n, Integral n) => Elaborated -> Inputs n -> Either (Error n) [Integer]
run elab inputs = fst <$> runAndOutputWitnesses elab inputs

--------------------------------------------------------------------------------

interpretExpr :: (GaloisField n, Integral n) => Expr -> M n [Integer]
interpretExpr expr = case expr of
  Unit -> return []
  Boolean e -> do
    result <- interpretB e
    case result of
      [True] -> return [1]
      _ -> return [0]
  Field e -> map toInteger <$> interpret e
  UInt e -> map U.uValue <$> interpretU e
  Array xs -> do
    result <- mapM interpretExpr xs
    return $ concat result

-- | For handling div/mod statements
-- we can solve a div/mod relation if we know:
--    1. dividend & divisor
--    1. dividend & quotient
--    2. divisor & quotient & remainder
interpretDivMod :: (GaloisField n, Integral n) => Width -> (UInt, UInt, UInt, UInt) -> M n ()
interpretDivMod width (dividendExpr, divisorExpr, quotientExpr, remainderExpr) = do
  dividend <- analyze dividendExpr
  divisor <- analyze divisorExpr
  quotient <- analyze quotientExpr
  remainder <- analyze remainderExpr
  case dividend of
    Left dividendVar -> do
      -- now that we don't know the dividend, we can only solve the relation if we know the divisor, quotient, and remainder
      -- case (divisor, quotient, remainder) of
      --   (Right divisorVal, Right quotientVal, Right remainderVal) -> do
      --     let dividendVal = U.new width (U.uValue divisorVal * U.uValue quotientVal + U.uValue remainderVal)
      --     addU width dividendVar [dividendVal]
      --   _ -> do
      let unsolvedVars = dividendVar : Either.lefts [divisor, quotient, remainder]
      throwError $ DivModStuckError unsolvedVars
    Right dividendVal -> do
      -- now that we know the dividend, we can solve the relation if we know either the divisor or the quotient
      case (divisor, quotient, remainder) of
        (Right divisorVal, Right actualQuotientVal, Right actualRemainderVal) -> do
          when (U.uValue divisorVal == 0) $
            throwError DivModDivisorIsZeroError
          let expectedQuotientVal = dividendVal `div` divisorVal
              expectedRemainderVal = dividendVal `mod` divisorVal
          if expectedQuotientVal == actualQuotientVal
            then return ()
            else throwError $ DivModQuotientError (U.uValue dividendVal) (U.uValue divisorVal) (U.uValue expectedQuotientVal) (U.uValue actualQuotientVal)
          if expectedRemainderVal == actualRemainderVal
            then return ()
            else throwError $ DivModRemainderError (U.uValue dividendVal) (U.uValue divisorVal) (U.uValue expectedRemainderVal) (U.uValue actualRemainderVal)
        (Right divisorVal, Left quotientVar, Left remainderVar) -> do
          when (U.uValue divisorVal == 0) $
            throwError DivModDivisorIsZeroError
          let quotientVal = dividendVal `div` divisorVal
              remainderVal = dividendVal `mod` divisorVal
          addU width quotientVar [quotientVal]
          addU width remainderVar [remainderVal]
        (Right divisorVal, Left quotientVar, Right actualRemainderVal) -> do
          when (U.uValue divisorVal == 0) $
            throwError DivModDivisorIsZeroError
          let quotientVal = dividendVal `div` divisorVal
              expectedRemainderVal = dividendVal `mod` divisorVal
          if expectedRemainderVal == actualRemainderVal
            then addU width quotientVar [quotientVal]
            else throwError $ DivModRemainderError (U.uValue dividendVal) (U.uValue divisorVal) (U.uValue expectedRemainderVal) (U.uValue actualRemainderVal)
        (Left divisorVar, Right quotientVal, Left remainderVar) -> do
          -- we cannot solve this relation if:
          --  1. quotient = 0
          --  2. dividend = 0 but quotient != 0
          (divisorVal, remainderVal) <-
            if U.uValue quotientVal == 0
              then throwError DivModQuotientIsZeroError
              else
                if U.uValue dividendVal == 0
                  then throwError DivModDividendIsZeroError
                  else return (dividendVal `divMod` quotientVal)
          addU width divisorVar [divisorVal]
          addU width remainderVar [remainderVal]
        (Left divisorVar, Right quotientVal, Right actualRemainderVal) -> do
          let divisorVal = dividendVal `div` quotientVal
              expectedRemainderVal = dividendVal `mod` divisorVal
          if expectedRemainderVal == actualRemainderVal
            then addU width divisorVar [divisorVal]
            else throwError $ DivModRemainderError (U.uValue dividendVal) (U.uValue divisorVal) (U.uValue expectedRemainderVal) (U.uValue actualRemainderVal)
        _ -> do
          let unsolvedVars = Either.lefts [divisor, quotient, remainder]
          throwError $ DivModStuckError unsolvedVars
  where
    analyze :: (GaloisField n, Integral n) => UInt -> M n (Either Var U)
    analyze = \case
      VarU w var -> catchError (Right <$> lookupU w var) $ \case
        VarUnboundError _ _ -> return (Left var)
        e -> throwError e
      x -> do
        xs <- interpretU x
        case xs of
          (v : _) -> return (Right v)
          _ -> throwError $ ResultSizeError 1 (length xs)

--------------------------------------------------------------------------------

instance (GaloisField n, Integral n) => Interpret SideEffect n where
  interpret (AssignmentB var val) = do
    interpretB val >>= addB var
    return []
  interpret (AssignmentF var val) = do
    interpret val >>= addF var
    return []
  interpret (AssignmentU width var val) = do
    interpretU val >>= addU width var
    return []
  interpret (DivMod width dividend divisor quotient remainder) = do
    interpretDivMod width (dividend, divisor, quotient, remainder)
    return []
  interpret (CLDivMod width dividend divisor quotient remainder) = do
    error "Interpret SideEffect CLDivMod"
  interpret (AssertLTE width value bound) = do
    -- check if the bound is within the range of the UInt
    when (bound < 0) $
      throwError $
        AssertLTEBoundTooSmallError bound
    when (bound >= 2 ^ width - 1) $
      throwError $
        AssertLTEBoundTooLargeError bound width
    value' <- interpretU value
    case value' of
      [v] -> do
        when (U.uValue v > bound) $ throwError $ AssertLTEError (U.uValue v) bound
        return []
      _ -> throwError $ ResultSizeError 1 (length value')
  interpret (AssertLT width value bound) = do
    -- check if the bound is within the range of the UInt
    when (bound < 1) $
      throwError $
        AssertLTBoundTooSmallError bound
    when (bound >= 2 ^ width) $
      throwError $
        AssertLTBoundTooLargeError bound width
    value' <- interpretU value
    case value' of
      [v] -> do
        when (U.uValue v >= bound) $ throwError $ AssertLTError (U.uValue v) bound
        return []
      _ -> throwError $ ResultSizeError 1 (length value')
  interpret (AssertGTE width value bound) = do
    -- check if the bound is within the range of the UInt
    when (bound < 1) $
      throwError $
        AssertGTEBoundTooSmallError bound
    when (bound >= 2 ^ width) $
      throwError $
        AssertGTEBoundTooLargeError bound width
    value' <- interpretU value
    case value' of
      [v] -> do
        when (U.uValue v < bound) $ throwError $ AssertGTEError (U.uValue v) bound
        return []
      _ -> throwError $ ResultSizeError 1 (length value')
  interpret (AssertGT width value bound) = do
    -- check if the bound is within the range of the UInt
    when (bound < 0) $
      throwError $
        AssertGTBoundTooSmallError bound
    when (bound >= 2 ^ width - 1) $
      throwError $
        AssertGTBoundTooLargeError bound width
    value' <- interpretU value
    case value' of
      [v] -> do
        when (U.uValue v <= bound) $ throwError $ AssertGTError (U.uValue v) bound
        return []
      _ -> throwError $ ResultSizeError 1 (length value')

instance GaloisField n => InterpretB Bool n where
  interpretB True = return [one]
  interpretB False = return [zero]

instance (GaloisField n, Integral n) => InterpretB Boolean n where
  interpretB expr = case expr of
    ValB b -> interpretB b
    VarB var -> pure <$> lookupB var
    VarBI var -> pure <$> lookupBI var
    VarBP var -> pure <$> lookupBP var
    AndB x y -> zipWith (.&.) <$> interpretB x <*> interpretB y
    OrB x y -> zipWith (.|.) <$> interpretB x <*> interpretB y
    XorB x y -> zipWith xor <$> interpretB x <*> interpretB y
    NotB x -> map not <$> interpretB x
    IfB p x y -> do
      p' <- interpretB p
      case p' of
        [True] -> interpretB x
        _ -> interpretB y
    EqB x y -> do
      x' <- interpretB x
      y' <- interpretB y
      interpretB (x' == y')
    EqF x y -> do
      x' <- interpret x
      y' <- interpret y
      interpretB (x' == y')
    EqU _ x y -> do
      x' <- interpretU x
      y' <- interpretU y
      interpretB (x' == y')
    LTU _ x y -> do
      x' <- interpretU x
      y' <- interpretU y
      interpretB (x' < y')
    LTEU _ x y -> do
      x' <- interpretU x
      y' <- interpretU y
      interpretB (x' <= y')
    GTU _ x y -> do
      x' <- interpretU x
      y' <- interpretU y
      interpretB (x' > y')
    GTEU _ x y -> do
      x' <- interpretU x
      y' <- interpretU y
      interpretB (x' >= y')
    BitU width x i -> do
      xs <- interpretU x
      if Data.Bits.testBit (U.uValue (head xs)) (i `mod` width)
        then return [one]
        else return [zero]

instance (GaloisField n, Integral n) => Interpret Field n where
  interpret expr = case expr of
    ValF n -> return [fromIntegral n]
    ValFR n -> return [fromRational n]
    VarF var -> pure <$> lookupF var
    VarFI var -> pure <$> lookupFI var
    VarFP var -> pure <$> lookupFP var
    AddF x y -> zipWith (+) <$> interpret x <*> interpret y
    SubF x y -> zipWith (-) <$> interpret x <*> interpret y
    MulF x y -> zipWith (*) <$> interpret x <*> interpret y
    ExpF x n -> map (^ n) <$> interpret x
    DivF x y -> zipWith (/) <$> interpret x <*> interpret y
    IfF p x y -> do
      p' <- interpretB p
      case p' of
        [True] -> interpret x
        _ -> interpret y
    BtoF x -> do
      result <- interpretB x
      case result of
        [True] -> return [one]
        _ -> return [zero]

instance (GaloisField n, Integral n) => InterpretU UInt n where
  interpretU expr = case expr of
    ValU w n -> return [U.new w n]
    VarU w var -> pure <$> lookupU w var
    VarUI w var -> pure <$> lookupUI w var
    VarUP w var -> pure <$> lookupUP w var
    AddU _ x y -> zipWith (+) <$> interpretU x <*> interpretU y
    SubU _ x y -> zipWith (-) <$> interpretU x <*> interpretU y
    CLMulU _ x y -> zipWith U.clMul <$> interpretU x <*> interpretU y
    MulU _ x y -> zipWith (*) <$> interpretU x <*> interpretU y
    MMIU w x p -> do
      x' <- map U.uValue <$> interpretU x
      case x' of
        [x''] -> case U.modInv x'' p of
          Just v -> do
            return [U.new w v]
          _ -> throwError $ ModInvError x'' p
        _ -> throwError $ ResultSizeError 1 (length x')
    AndU _ x y -> zipWith (.&.) <$> interpretU x <*> interpretU y
    OrU _ x y -> zipWith (.|.) <$> interpretU x <*> interpretU y
    XorU _ x y -> zipWith xor <$> interpretU x <*> interpretU y
    NotU _ x -> map complement <$> interpretU x
    RoLU _ i x -> map (`rotateL` i) <$> interpretU x
    ShLU _ i x -> map (`shiftL` i) <$> interpretU x
    SetU _ x i y -> zipWith (\x' val -> if val then setBit x' i else clearBit x' i) <$> interpretU x <*> interpretB y
    IfU _ p x y -> do
      p' <- interpretB p
      case p' of
        [True] -> interpretU x
        _ -> interpretU y
    BtoU w x -> do
      result <- interpretB x
      case result of
        [True] -> return [U.new w 1]
        _ -> return [U.new w 0]

-- instance (GaloisField n, Integral n) => Interpret Expr n where
--   interpret expr = case expr of
--     Unit -> return []
--     Boolean e -> do
--       result <- interpretB e
--       case result of
--         [True] -> return [one]
--         _ -> return [zero]
--     Field e -> interpret e
--     UInt e -> map (fromInteger . U.uValue) <$> interpretU e
--     Array xs -> concat <$> mapM interpret xs

--------------------------------------------------------------------------------

instance GaloisField n => Interpret () n where
  interpret val = case val of
    () -> return []

instance (Interpret t1 n, Interpret t2 n, GaloisField n) => Interpret (t1, t2) n where
  interpret (a, b) = liftM2 (<>) (interpret a) (interpret b)

instance (Interpret t n, GaloisField n) => Interpret [t] n where
  interpret xs = concat <$> mapM interpret xs

-- instance (GaloisField n, Integral n) => Interpret (ArrM t) n where
--   interpret val = case val of
--     ArrayRef _elemType _len addr -> do
--       heap <- ask
--       case IntMap.lookup addr heap of
--         Nothing -> error "[ panic ] address not found when trying to read heap"
--         Just (elemType, vars) -> case elemType of
--           ElemF -> interpret $ map VarF (toList vars)
--           ElemB -> interpret $ map VarB (toList vars)
--           ElemU width -> mapM (lookupU width) (toList vars)
--           ElemArr elemType' len -> concat <$> mapM (interpret . ArrayRef elemType' len) (toList vars)
--           EmptyArr -> return []

--------------------------------------------------------------------------------

instance FreeVar Expr where
  freeVars expr = case expr of
    Unit -> mempty
    Boolean e -> freeVars e
    Field e -> freeVars e
    UInt e -> freeVars e
    Array xs -> mconcat $ map freeVars (toList xs)

-- | Collect free variables of an elaborated program (that should also be present in the witness)
instance FreeVar Elaborated where
  freeVars (Elaborated value context) = freeVars value <> freeVars context

instance FreeVar Computation where
  freeVars context =
    mconcat
      [ mconcat $ map freeVars (toList (compSideEffects context)),
        mconcat $ map freeVars (toList (compAssertions context))
      ]

instance FreeVar SideEffect where
  freeVars (AssignmentF var field) = modifyX (modifyF (IntSet.insert var)) (freeVars field)
  freeVars (AssignmentB var bool) = modifyX (modifyB (IntSet.insert var)) (freeVars bool)
  freeVars (AssignmentU width var uint) = modifyX (modifyU width mempty (IntSet.insert var)) (freeVars uint)
  freeVars (DivMod _width x y q r) = freeVars x <> freeVars y <> freeVars q <> freeVars r
  freeVars (CLDivMod _width x y q r) = freeVars x <> freeVars y <> freeVars q <> freeVars r
  freeVars (AssertLTE _width x _) = freeVars x
  freeVars (AssertLT _width x _) = freeVars x
  freeVars (AssertGTE _width x _) = freeVars x
  freeVars (AssertGT _width x _) = freeVars x

instance FreeVar Boolean where
  freeVars expr = case expr of
    ValB _ -> mempty
    VarB var -> modifyX (modifyB (IntSet.insert var)) mempty
    VarBI var -> modifyI (modifyB (IntSet.insert var)) mempty
    VarBP var -> modifyP (modifyB (IntSet.insert var)) mempty
    AndB x y -> freeVars x <> freeVars y
    OrB x y -> freeVars x <> freeVars y
    XorB x y -> freeVars x <> freeVars y
    NotB x -> freeVars x
    IfB p x y -> freeVars p <> freeVars x <> freeVars y
    EqB x y -> freeVars x <> freeVars y
    EqF x y -> freeVars x <> freeVars y
    EqU _ x y -> freeVars x <> freeVars y
    LTU _ x y -> freeVars x <> freeVars y
    LTEU _ x y -> freeVars x <> freeVars y
    GTU _ x y -> freeVars x <> freeVars y
    GTEU _ x y -> freeVars x <> freeVars y
    BitU _ x _ -> freeVars x

instance FreeVar Field where
  freeVars expr = case expr of
    ValF _ -> mempty
    ValFR _ -> mempty
    VarF var -> modifyX (modifyF (IntSet.insert var)) mempty
    VarFI var -> modifyI (modifyF (IntSet.insert var)) mempty
    VarFP var -> modifyP (modifyF (IntSet.insert var)) mempty
    AddF x y -> freeVars x <> freeVars y
    SubF x y -> freeVars x <> freeVars y
    MulF x y -> freeVars x <> freeVars y
    ExpF x _ -> freeVars x
    DivF x y -> freeVars x <> freeVars y
    IfF p x y -> freeVars p <> freeVars x <> freeVars y
    BtoF x -> freeVars x

instance FreeVar UInt where
  freeVars expr = case expr of
    ValU _ _ -> mempty
    VarU w var -> modifyX (modifyU w mempty (IntSet.insert var)) mempty
    VarUI w var -> modifyI (modifyU w mempty (IntSet.insert var)) mempty
    VarUP w var -> modifyP (modifyU w mempty (IntSet.insert var)) mempty
    AddU _ x y -> freeVars x <> freeVars y
    SubU _ x y -> freeVars x <> freeVars y
    MulU _ x y -> freeVars x <> freeVars y
    CLMulU _ x y -> freeVars x <> freeVars y
    MMIU _ x _ -> freeVars x
    AndU _ x y -> freeVars x <> freeVars y
    OrU _ x y -> freeVars x <> freeVars y
    XorU _ x y -> freeVars x <> freeVars y
    NotU _ x -> freeVars x
    RoLU _ _ x -> freeVars x
    ShLU _ _ x -> freeVars x
    SetU _ x _ y -> freeVars x <> freeVars y
    IfU _ p x y -> freeVars p <> freeVars x <> freeVars y
    BtoU _ x -> freeVars x

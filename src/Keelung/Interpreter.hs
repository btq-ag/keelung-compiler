-- Interpreter for Keelung.Syntax.Encode.Syntax
{-# LANGUAGE FlexibleInstances #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Interpreter (runAndOutputWitnesses, run, interpretDivMod, interpretCLDivMod, Error (..)) where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Bits (Bits (..))
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntSet qualified as IntSet
import Data.Semiring (Semiring (..))
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Data.FieldInfo (FieldInfo)
import Keelung.Data.FieldInfo qualified as FieldInfo
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Data.VarGroup
import Keelung.Interpreter.Monad
import Keelung.Syntax (Var, Width)
import Keelung.Syntax.Encode.Syntax

--------------------------------------------------------------------------------

-- | Interpret a program with inputs and return outputs along with the witness
runAndOutputWitnesses :: (GaloisField n, Integral n) => FieldInfo -> Elaborated -> Inputs n -> Either (Error n) ([Integer], Witness Integer Integer Integer)
runAndOutputWitnesses fieldInfo (Elaborated expr comp) inputs = runM mempty fieldInfo inputs $ do
  -- interpret side-effects
  forM_ (compSideEffects comp) $ \sideEffect -> void (interpretU sideEffect)

  -- interpret the assertions next
  -- throw error if any assertion fails
  forM_ (compAssertions comp) $ \e -> do
    values <- interpretExpr e
    when (values /= [1]) $ do
      -- collect variables and their bindings in the expression and report them
      throwError $ AssertionError (show e)
  -- lastly interpret the expression and return the result
  interpretExpr expr

-- | Interpret a program with inputs.
run :: (GaloisField n, Integral n) => FieldInfo -> Elaborated -> Inputs n -> Either (Error n) [Integer]
run fieldInfo elab inputs = fst <$> runAndOutputWitnesses fieldInfo elab inputs

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
  UInt e -> map toInteger <$> interpretU e
  Array xs -> do
    result <- mapM interpretExpr xs
    return $ concat result

-- | For handling div/mod statements
interpretDivMod :: (GaloisField n, Integral n) => Width -> (UInt, UInt, UInt, UInt) -> M n ()
interpretDivMod = interpretDivModPrim False

-- | For handling carry-less div/mod statements
interpretCLDivMod :: (GaloisField n, Integral n) => Width -> (UInt, UInt, UInt, UInt) -> M n ()
interpretCLDivMod = interpretDivModPrim True

-- | We can solve a div/mod relation if we know:
--    1. dividend & divisor
--    2. dividend & quotient
--    3. divisor & quotient
--    4. divisor & quotient & remainder
interpretDivModPrim :: (GaloisField n, Integral n) => Bool -> Width -> (UInt, UInt, UInt, UInt) -> M n ()
interpretDivModPrim isCarryLess width (dividendExpr, divisorExpr, quotientExpr, remainderExpr) = do
  dividend <- analyze dividendExpr
  divisor <- analyze divisorExpr
  quotient <- analyze quotientExpr
  remainder <- analyze remainderExpr
  case dividend of
    Left dividendVar -> do
      -- now that we don't know the dividend, we can only solve the relation if we know the divisor, quotient, and remainder
      case (divisor, quotient, remainder) of
        (Right divisorVal, Right quotientVal, Right remainderVal) -> do
          let dividendVal =
                if isCarryLess
                  then U.clMul quotientVal divisorVal `U.clAdd` remainderVal
                  else U.new width (toInteger divisorVal * toInteger quotientVal + toInteger remainderVal)
          addU width dividendVar [dividendVal]
        (Right _, Right _, Left _) -> throwError $ DivModCannotInferDividendError True True False
        (Right _, Left _, Right _) -> throwError $ DivModCannotInferDividendError True False True
        (Right _, Left _, Left _) -> throwError $ DivModCannotInferDividendError True False False
        (Left _, Right _, Right _) -> throwError $ DivModCannotInferDividendError False True True
        (Left _, Right _, Left _) -> throwError $ DivModCannotInferDividendError False True False
        (Left _, Left _, Right _) -> throwError $ DivModCannotInferDividendError False False True
        (Left _, Left _, Left _) -> throwError $ DivModCannotInferDividendError False False False
    Right dividendVal -> do
      -- now that we know the dividend, we can solve the relation if we know either the divisor or the quotient
      case (divisor, quotient, remainder) of
        (Right divisorVal, Right actualQuotientVal, Right actualRemainderVal) -> do
          when (toInteger divisorVal == 0) $
            throwError DivModDivisorIsZeroError
          let (expectedQuotientVal, expectedRemainderVal) =
                if isCarryLess
                  then dividendVal `U.clDivMod` divisorVal
                  else dividendVal `divMod` divisorVal
          if expectedQuotientVal == actualQuotientVal
            then return ()
            else throwError $ DivModQuotientError isCarryLess (toInteger dividendVal) (toInteger divisorVal) (toInteger expectedQuotientVal) (toInteger actualQuotientVal)
          if expectedRemainderVal == actualRemainderVal
            then return ()
            else throwError $ DivModRemainderError isCarryLess (toInteger dividendVal) (toInteger divisorVal) (toInteger expectedRemainderVal) (toInteger actualRemainderVal)
        (Right divisorVal, Right quotientVal, Left remainderVar) -> do
          when (toInteger divisorVal == 0) $
            throwError DivModDivisorIsZeroError
          let (expectedQuotientVal, expectedRemainderVal) =
                if isCarryLess
                  then dividendVal `U.clDivMod` divisorVal
                  else dividendVal `divMod` divisorVal
          if expectedQuotientVal == quotientVal
            then addU width remainderVar [expectedRemainderVal]
            else throwError $ DivModQuotientError isCarryLess (toInteger dividendVal) (toInteger divisorVal) (toInteger expectedQuotientVal) (toInteger quotientVal)
        (Right divisorVal, Left quotientVar, Right actualRemainderVal) -> do
          when (toInteger divisorVal == 0) $
            throwError DivModDivisorIsZeroError
          let (quotientVal, expectedRemainderVal) =
                if isCarryLess
                  then dividendVal `U.clDivMod` divisorVal
                  else dividendVal `divMod` divisorVal
          if expectedRemainderVal == actualRemainderVal
            then addU width quotientVar [quotientVal]
            else throwError $ DivModRemainderError isCarryLess (toInteger dividendVal) (toInteger divisorVal) (toInteger expectedRemainderVal) (toInteger actualRemainderVal)
        (Right divisorVal, Left quotientVar, Left remainderVar) -> do
          when (toInteger divisorVal == 0) $
            throwError DivModDivisorIsZeroError
          let (quotientVal, remainderVal) =
                if isCarryLess
                  then dividendVal `U.clDivMod` divisorVal
                  else dividendVal `divMod` divisorVal
          addU width quotientVar [quotientVal]
          addU width remainderVar [remainderVal]
        (Left divisorVar, Right quotientVal, Right actualRemainderVal) -> do
          let divisorVal =
                if isCarryLess
                  then dividendVal `U.clDiv` quotientVal
                  else dividendVal `div` quotientVal
              expectedRemainderVal =
                if isCarryLess
                  then dividendVal `U.clMod` divisorVal
                  else dividendVal `mod` divisorVal
          if expectedRemainderVal == actualRemainderVal
            then addU width divisorVar [divisorVal]
            else throwError $ DivModRemainderError isCarryLess (toInteger dividendVal) (toInteger divisorVal) (toInteger expectedRemainderVal) (toInteger actualRemainderVal)
        (Left divisorVar, Right quotientVal, Left remainderVar) -> do
          -- we cannot solve this relation if:
          --  1. quotient = 0
          --  2. dividend = 0 but quotient != 0
          (divisorVal, remainderVal) <-
            if toInteger quotientVal == 0
              then throwError DivModQuotientIsZeroError
              else
                if toInteger dividendVal == 0
                  then throwError DivModDividendIsZeroError
                  else
                    if isCarryLess
                      then return (dividendVal `U.clDivMod` quotientVal)
                      else return (dividendVal `divMod` quotientVal)
          addU width divisorVar [divisorVal]
          addU width remainderVar [remainderVal]
        (Left _, Left _, Right _) -> throwError DivModDivisorAndQuotientUnknownError
        (Left _, Left _, Left _) -> throwError DivModDivisorAndQuotientAndRemainderUnknownError
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

-- -- | For handling carry-less div/mod statements
-- -- we can solve a carry-less div/mod relation if we know:
-- --    1. dividend & divisor
-- --    1. dividend & quotient
-- --    2. divisor & quotient & remainder
-- interpretCLDivMod :: (GaloisField n, Integral n) => Width -> (UInt, UInt, UInt, UInt) -> M n ()
-- interpretCLDivMod width (dividendExpr, divisorExpr, quotientExpr, remainderExpr) = do
--   dividend <- analyze dividendExpr
--   divisor <- analyze divisorExpr
--   quotient <- analyze quotientExpr
--   remainder <- analyze remainderExpr
--   case dividend of
--     Left dividendVar -> do
--       let unsolvedVars = dividendVar : Either.lefts [divisor, quotient, remainder]
--       throwError $ DivModStuckError True unsolvedVars
--     Right dividendVal -> do
--       -- now that we know the dividend, we can solve the relation if we know either the divisor or the quotient
--       case (divisor, quotient, remainder) of
--         (Right divisorVal, Right actualQuotientVal, Right actualRemainderVal) -> do
--           when (toInteger divisorVal == 0) $
--             throwError DivModDivisorIsZeroError
--           let (expectedQuotientVal, expectedRemainderVal) = dividendVal `U.clDivMod` divisorVal
--           if expectedQuotientVal == actualQuotientVal
--             then return ()
--             else throwError $ DivModQuotientError True (toInteger dividendVal) (toInteger divisorVal) (toInteger expectedQuotientVal) (toInteger actualQuotientVal)
--           if expectedRemainderVal == actualRemainderVal
--             then return ()
--             else throwError $ DivModRemainderError True (toInteger dividendVal) (toInteger divisorVal) (toInteger expectedRemainderVal) (toInteger actualRemainderVal)
--         (Right divisorVal, Left quotientVar, Left remainderVar) -> do
--           when (toInteger divisorVal == 0) $
--             throwError DivModDivisorIsZeroError
--           let (quotientVal, remainderVal) = dividendVal `U.clDivMod` divisorVal
--           addU width quotientVar [quotientVal]
--           addU width remainderVar [remainderVal]
--         (Right divisorVal, Left quotientVar, Right actualRemainderVal) -> do
--           when (toInteger divisorVal == 0) $
--             throwError DivModDivisorIsZeroError
--           let (quotientVal, expectedRemainderVal) = dividendVal `U.clDivMod` divisorVal
--           if expectedRemainderVal == actualRemainderVal
--             then addU width quotientVar [quotientVal]
--             else throwError $ DivModRemainderError True (toInteger dividendVal) (toInteger divisorVal) (toInteger expectedRemainderVal) (toInteger actualRemainderVal)
--         (Left divisorVar, Right quotientVal, Left remainderVar) -> do
--           -- we cannot solve this relation if:
--           --  1. quotient = 0
--           --  2. dividend = 0 but quotient != 0
--           (divisorVal, remainderVal) <-
--             if toInteger quotientVal == 0
--               then throwError DivModQuotientIsZeroError
--               else
--                 if toInteger dividendVal == 0
--                   then throwError DivModDividendIsZeroError
--                   else return (dividendVal `divMod` quotientVal)
--           addU width divisorVar [divisorVal]
--           addU width remainderVar [remainderVal]
--         (Left divisorVar, Right quotientVal, Right actualRemainderVal) -> do
--           let divisorVal = dividendVal `U.clDiv` quotientVal
--               expectedRemainderVal = dividendVal `U.clMod` divisorVal
--           if expectedRemainderVal == actualRemainderVal
--             then addU width divisorVar [divisorVal]
--             else throwError $ DivModRemainderError True (toInteger dividendVal) (toInteger divisorVal) (toInteger expectedRemainderVal) (toInteger actualRemainderVal)
--         _ -> do
--           let unsolvedVars = Either.lefts [divisor, quotient, remainder]
--           throwError $ DivModStuckError True unsolvedVars
--   where
--     analyze :: (GaloisField n, Integral n) => UInt -> M n (Either Var U)
--     analyze = \case
--       VarU w var -> catchError (Right <$> lookupU w var) $ \case
--         VarUnboundError _ _ -> return (Left var)
--         e -> throwError e
--       x -> do
--         xs <- interpretU x
--         case xs of
--           (v : _) -> return (Right v)
--           _ -> throwError $ ResultSizeError 1 (length xs)

--------------------------------------------------------------------------------

instance (GaloisField n, Integral n) => InterpretU SideEffect n where
  interpretU (AssignmentB var val) = do
    interpretB val >>= addB var
    return []
  interpretU (AssignmentF var val) = do
    interpret val >>= addF var
    return []
  interpretU (AssignmentU width var val) = do
    interpretU val >>= addU width var
    return []
  interpretU (ToUInt width varU varF) = do
    -- get the bit width of the underlying field
    fieldWidth <- asks (FieldInfo.fieldWidth . snd)
    -- UInt bits beyond `fieldWidth` are ignored
    valU <- existsU width varU
    valF <- existsF varF
    case (valU, valF) of
      (Nothing, Nothing) -> return () -- both are not in the bindings
      (Just u, Nothing) -> addF varF [fromInteger $ truncateUInt fieldWidth u]
      (Nothing, Just f) -> addU width varU [U.new width (fromIntegral f)]
      (Just u, Just f) -> do
        when (truncateUInt fieldWidth u /= toInteger f) $ throwError $ RelateUFError u f
    return []
    where
      truncateUInt :: Width -> U -> Integer
      truncateUInt desiredWidth u = toInteger u `mod` (2 ^ desiredWidth)
  interpretU (ToField width varU varF) = do
    -- get the bit width of the underlying field
    fieldWidth <- asks (FieldInfo.fieldWidth . snd)
    -- UInt bits beyond `fieldWidth` are ignored
    valU <- existsU width varU
    valF <- existsF varF
    case (valU, valF) of
      (Nothing, Nothing) -> return () -- both are not in the bindings
      (Just u, Nothing) -> addF varF [fromInteger $ truncateUInt fieldWidth u]
      (Nothing, Just f) -> addU width varU [U.new width (fromIntegral f)]
      (Just u, Just f) -> do
        when (truncateUInt fieldWidth u /= toInteger f) $ throwError $ RelateUFError u f
    return []
    where
      truncateUInt :: Width -> U -> Integer
      truncateUInt desiredWidth u = toInteger u `mod` (2 ^ desiredWidth)
  interpretU (BitsToUInt width varU bools) = do
    bools' <- mapM interpretB bools
    let value = U.new width $ foldr (\b acc -> acc * 2 + if b then 1 else 0) 0 (concat bools')
    addU width varU [value]
    return [value]
  interpretU (DivMod width dividend divisor quotient remainder) = do
    interpretDivMod width (dividend, divisor, quotient, remainder)
    return []
  interpretU (CLDivMod width dividend divisor quotient remainder) = do
    interpretCLDivMod width (dividend, divisor, quotient, remainder)
    return []
  interpretU (AssertLTE width value bound) = do
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
        when (toInteger v > bound) $ throwError $ AssertLTEError (toInteger v) bound
        return []
      _ -> throwError $ ResultSizeError 1 (length value')
  interpretU (AssertLT width value bound) = do
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
        when (toInteger v >= bound) $ throwError $ AssertLTError (toInteger v) bound
        return []
      _ -> throwError $ ResultSizeError 1 (length value')
  interpretU (AssertGTE width value bound) = do
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
        when (toInteger v < bound) $ throwError $ AssertGTEError (toInteger v) bound
        return []
      _ -> throwError $ ResultSizeError 1 (length value')
  interpretU (AssertGT width value bound) = do
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
        when (toInteger v <= bound) $ throwError $ AssertGTError (toInteger v) bound
        return []
      _ -> throwError $ ResultSizeError 1 (length value')

instance (GaloisField n) => InterpretB Bool n where
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
      if Data.Bits.testBit (toInteger (head xs)) (i `mod` width)
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
    ExpF x n -> do
      x' <- interpret x
      if x' == [0] && n == 0
        then return [1]
        else map (^ n) <$> interpret x
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
    AddV w xs -> map (U.slice (0, w)) <$> (foldr (zipWith (+)) [U.new w 0] <$> mapM (interpretU . overwriteWidth w) xs)
    SubU _ x y -> zipWith (-) <$> interpretU x <*> interpretU y
    CLMulU _ x y -> zipWith U.clMul <$> interpretU x <*> interpretU y
    MulU w x y -> zipWith (U.mulV w) <$> interpretU x <*> interpretU y
    AESMulU _ x y -> zipWith U.aesMul <$> interpretU x <*> interpretU y
    MMIU w x p -> do
      x' <- map toInteger <$> interpretU x
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
    SliceU _ x i j -> do
      xs <- interpretU x
      return (map (U.slice (i, j)) xs)
    JoinU _ x y -> do
      xs <- interpretU x
      ys <- interpretU y
      return [U.join x' y' | (x', y') <- zip xs ys]

-- | overwriting the width of a UInt expression
overwriteWidth :: Width -> UInt -> UInt
overwriteWidth w expr = case expr of
  ValU _ n -> ValU w n
  VarU v var -> VarU v var -- variable width is not changed
  VarUI v var -> VarUI v var -- variable width is not changed
  VarUP v var -> VarUP v var -- variable width is not changed
  AddU _ x y -> AddU w (overwriteWidth w x) (overwriteWidth w y)
  AddV _ xs -> AddV w (map (overwriteWidth w) xs)
  SubU _ x y -> SubU w (overwriteWidth w x) (overwriteWidth w y)
  CLMulU _ x y -> CLMulU w (overwriteWidth w x) (overwriteWidth w y)
  MulU _ x y -> MulU w (overwriteWidth w x) (overwriteWidth w y)
  AESMulU _ x y -> AESMulU w (overwriteWidth w x) (overwriteWidth w y)
  MMIU _ x p -> MMIU w (overwriteWidth w x) p
  AndU _ x y -> AndU w (overwriteWidth w x) (overwriteWidth w y)
  OrU _ x y -> OrU w (overwriteWidth w x) (overwriteWidth w y)
  XorU _ x y -> XorU w (overwriteWidth w x) (overwriteWidth w y)
  NotU _ x -> NotU w (overwriteWidth w x)
  RoLU _ i x -> RoLU w i (overwriteWidth w x)
  ShLU _ i x -> ShLU w i (overwriteWidth w x)
  SetU _ x i y -> SetU w (overwriteWidth w x) i y
  IfU _ p x y -> IfU w p (overwriteWidth w x) (overwriteWidth w y)
  BtoU _ x -> BtoU w x
  SliceU _ x i j -> SliceU w (overwriteWidth w x) i j
  JoinU _ x y -> JoinU w (overwriteWidth w x) (overwriteWidth w y)

-- instance (GaloisField n, Integral n) => Interpret Expr n where
--   interpret expr = case expr of
--     Unit -> return []
--     Boolean e -> do
--       result <- interpretB e
--       case result of
--         [True] -> return [one]
--         _ -> return [zero]
--     Field e -> interpret e
--     UInt e -> map (fromInteger . toInteger) <$> interpretU e
--     Array xs -> concat <$> mapM interpret xs

--------------------------------------------------------------------------------

instance (GaloisField n) => Interpret () n where
  interpret val = case val of
    () -> return []

instance (Interpret t1 n, Interpret t2 n, GaloisField n) => Interpret (t1, t2) n where
  interpret (a, b) = liftM2 (<>) (interpret a) (interpret b)

instance (Interpret t n, GaloisField n) => Interpret [t] n where
  interpret xs = concat <$> mapM interpret xs

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
  freeVars (ToUInt width varU varF) = modifyX (modifyU width mempty (IntSet.insert varU)) $ modifyX (modifyF (IntSet.insert varF)) mempty
  freeVars (ToField width varU varF) = modifyX (modifyU width mempty (IntSet.insert varU)) $ modifyX (modifyF (IntSet.insert varF)) mempty
  freeVars (BitsToUInt width varU bools) = modifyX (modifyU width mempty (IntSet.insert varU)) $ mconcat (map freeVars bools)
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
    AddV _ xs -> mconcat (map freeVars xs)
    SubU _ x y -> freeVars x <> freeVars y
    MulU _ x y -> freeVars x <> freeVars y
    AESMulU _ x y -> freeVars x <> freeVars y
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
    SliceU _ x _ _ -> freeVars x
    JoinU _ x y -> freeVars x <> freeVars y

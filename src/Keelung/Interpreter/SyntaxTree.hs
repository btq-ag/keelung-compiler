-- Interpreter for Keelung.Syntax.Encode.Syntax
{-# LANGUAGE FlexibleInstances #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Interpreter.SyntaxTree (runAndOutputWitnesses, run, interpretDivMod, Error (..)) where

import Control.Monad.Except
import Control.Monad.State
import Data.Bits (Bits (..))
import Data.Either qualified as Either
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntSet qualified as IntSet
import Data.Semiring (Semiring (..))
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Data.Struct
import Keelung.Data.VarGroup
import Keelung.Data.VarGroup qualified as Bindings
import Keelung.Interpreter.Arithmetics
import Keelung.Interpreter.SyntaxTree.Monad
import Keelung.Syntax (Var, Width)
import Keelung.Syntax.Encode.Syntax

--------------------------------------------------------------------------------

-- | Interpret a program with inputs and return outputs along with the witness
runAndOutputWitnesses :: (GaloisField n, Integral n) => Elaborated -> Inputs n -> Either (Error n) ([n], Witness n)
runAndOutputWitnesses (Elaborated expr comp) inputs = runM mempty inputs $ do
  -- interpret assignments of values first
  -- fs <-
  --   filterM
  --     ( \(var, e) -> case e of
  --         ValF val -> interpret val >>= addF var >> return False
  --         _ -> return True
  --     )
  --     (IntMap.toList (structF (compExprBindings comp)))
  -- bs <-
  --   filterM
  --     ( \(var, e) -> case e of
  --         ValB val -> interpret val >>= addB var >> return False
  --         _ -> return True
  --     )
  --     (IntMap.toList (structB (compExprBindings comp)))
  -- us <-
  --   mapM
  --     ( \(width, xs) ->
  --         (width,)
  --           <$> filterM
  --             ( \(var, e) -> case e of
  --                 ValU _ val -> interpret val >>= addU width var >> return False
  --                 _ -> return True
  --             )
  --             (IntMap.toList xs)
  --     )
  --     (IntMap.toList (structU (compExprBindings comp)))

  -- -- interpret the rest of the assignments
  -- forM_ fs $ \(var, e) -> interpret e >>= addF var
  -- forM_ bs $ \(var, e) -> interpret e >>= addB var
  -- forM_ us $ \(width, xs) ->
  --   forM_ xs $ \(var, e) -> interpret e >>= addU width var

  -- interpret div/mod statements
  -- forM_ (IntMap.toList (compDivModRelsU comp)) $ \(width, xs) -> forM_ (reverse xs) (interpretDivMod width)

  -- interpret side-effects
  forM_ (compSideEffects comp) $ \sideEffect -> void $ interpret sideEffect

  -- interpret the assertions next
  -- throw error if any assertion fails
  forM_ (compAssertions comp) $ \e -> do
    values <- interpret e
    when (values /= [1]) $ do
      bindings <- get
      let bindingsInExpr = Bindings.restrictVars bindings (freeVars e)
      -- collect variables and their bindings in the expression and report them
      throwError $ AssertionError bindingsInExpr (show e)

  -- lastly interpret the expression and return the result
  interpret expr

-- | Interpret a program with inputs.
run :: (GaloisField n, Integral n) => Elaborated -> Inputs n -> Either (Error n) [n]
run elab inputs = fst <$> runAndOutputWitnesses elab inputs

--------------------------------------------------------------------------------

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
      case (divisor, quotient, remainder) of
        (Right divisorVal, Right quotientVal, Right remainderVal) -> do
          let dividendVal = divisorVal * quotientVal + remainderVal
          addU width dividendVar [dividendVal]
        _ -> do
          let unsolvedVars = dividendVar : Either.lefts [divisor, quotient, remainder]
          throwError $ StuckError "" unsolvedVars
    Right dividendVal -> do
      -- now that we know the dividend, we can solve the relation if we know either the divisor or the quotient
      case (divisor, quotient, remainder) of
        (Right divisorVal, Right actualQuotientVal, Right actualRemainderVal) -> do
          let expectedQuotientVal = dividendVal `integerDiv` divisorVal
              expectedRemainderVal = dividendVal `integerMod` divisorVal
          if expectedQuotientVal == actualQuotientVal
            then return ()
            else throwError $ DivModQuotientError dividendVal divisorVal expectedQuotientVal actualQuotientVal
          if expectedRemainderVal == actualRemainderVal
            then return ()
            else throwError $ DivModRemainderError dividendVal divisorVal expectedRemainderVal actualRemainderVal
        (Right divisorVal, Left quotientVar, Left remainderVar) -> do
          let quotientVal = dividendVal `integerDiv` divisorVal
              remainderVal = dividendVal `integerMod` divisorVal
          addU width quotientVar [quotientVal]
          addU width remainderVar [remainderVal]
        (Right divisorVal, Left quotientVar, Right actualRemainderVal) -> do
          let quotientVal = dividendVal `integerDiv` divisorVal
              expectedRemainderVal = dividendVal `integerMod` divisorVal
          if expectedRemainderVal == actualRemainderVal
            then addU width quotientVar [quotientVal]
            else throwError $ DivModRemainderError dividendVal divisorVal expectedRemainderVal actualRemainderVal
        (Left divisorVar, Right quotientVal, Left remainderVar) -> do
          let divisorVal = dividendVal `integerDiv` quotientVal
              remainderVal = dividendVal `integerMod` divisorVal
          addU width divisorVar [divisorVal]
          addU width remainderVar [remainderVal]
        (Left divisorVar, Right quotientVal, Right actualRemainderVal) -> do
          let divisorVal = dividendVal `integerDiv` quotientVal
              expectedRemainderVal = dividendVal `integerMod` divisorVal
          if expectedRemainderVal == actualRemainderVal
            then addU width divisorVar [divisorVal]
            else throwError $ DivModRemainderError dividendVal divisorVal expectedRemainderVal actualRemainderVal
        _ -> do
          let unsolvedVars = Either.lefts [divisor, quotient, remainder]
          throwError $ StuckError "" unsolvedVars
  where
    analyze :: (GaloisField n, Integral n) => UInt -> M n (Either Var n)
    analyze = \case
      VarU w var -> catchError (Right <$> lookupU w var) $ \case
        VarUnboundError _ _ -> return (Left var)
        e -> throwError e
      x -> do
        xs <- interpret x
        case xs of
          (v : _) -> return (Right v)
          _ -> throwError $ ResultSizeError 1 (length xs)

--------------------------------------------------------------------------------

instance (GaloisField n, Integral n) => Interpret SideEffect n where
  interpret (AssignmentB var val) = do
    interpret val >>= addB var
    return []
  interpret (AssignmentF var val) = do
    interpret val >>= addF var
    return []
  interpret (AssignmentU width var val) = do
    interpret val >>= addU width var
    return []
  interpret (DivMod width dividend divisor quotient remainder) = do
    interpretDivMod width (dividend, divisor, quotient, remainder)
    return []

instance GaloisField n => Interpret Bool n where
  interpret True = return [one]
  interpret False = return [zero]

instance (GaloisField n, Integral n) => Interpret Boolean n where
  interpret expr = case expr of
    ValB b -> interpret b
    VarB var -> pure <$> lookupB var
    VarBI var -> pure <$> lookupBI var
    VarBP var -> pure <$> lookupBP var
    AndB x y -> zipWith bitWiseAnd <$> interpret x <*> interpret y
    OrB x y -> zipWith bitWiseOr <$> interpret x <*> interpret y
    XorB x y -> zipWith bitWiseXor <$> interpret x <*> interpret y
    NotB x -> map bitWiseNot <$> interpret x
    IfB p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
    EqB x y -> do
      x' <- interpret x
      y' <- interpret y
      interpret (x' == y')
    EqF x y -> do
      x' <- interpret x
      y' <- interpret y
      interpret (x' == y')
    EqU _ x y -> do
      x' <- interpret x
      y' <- interpret y
      interpret (x' == y')
    BitU width x i -> do
      xs <- interpret x
      if Data.Bits.testBit (toInteger (head xs)) (i `mod` width)
        then return [one]
        else return [zero]

instance GaloisField n => Interpret Integer n where
  interpret n = return [fromIntegral n]

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
    DivF x y -> zipWith (/) <$> interpret x <*> interpret y
    IfF p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
    BtoF x -> interpret x

instance (GaloisField n, Integral n) => Interpret UInt n where
  interpret expr = case expr of
    ValU _ n -> return [fromIntegral n]
    VarU w var -> pure <$> lookupU w var
    VarUI w var -> pure <$> lookupUI w var
    VarUP w var -> pure <$> lookupUP w var
    AddU w x y -> wrapAround w $ zipWith (+) <$> interpret x <*> interpret y
    SubU w x y -> wrapAround w $ zipWith (-) <$> interpret x <*> interpret y
    MulU w x y -> wrapAround w $ zipWith (*) <$> interpret x <*> interpret y
    AndU _ x y -> zipWith bitWiseAnd <$> interpret x <*> interpret y
    OrU _ x y -> zipWith bitWiseOr <$> interpret x <*> interpret y
    XorU _ x y -> zipWith bitWiseXor <$> interpret x <*> interpret y
    NotU _ x -> map bitWiseNot <$> interpret x
    RoLU w i x -> map (bitWiseRotateL w i) <$> interpret x
    ShLU w i x -> map (bitWiseShiftL w i) <$> interpret x
    SetU w x i y -> zipWith (\x' y' -> bitWiseSet w x' i y') <$> interpret x <*> interpret y
    IfU _ p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
    BtoU _ x -> interpret x
    where
      wrapAround :: (GaloisField n, Integral n) => Int -> M n [n] -> M n [n]
      wrapAround width = fmap (map (fromInteger . (`mod` 2 ^ width) . toInteger))

instance (GaloisField n, Integral n) => Interpret Expr n where
  interpret expr = case expr of
    Unit -> return []
    Boolean e -> interpret e
    Field e -> interpret e
    UInt e -> interpret e
    Array xs -> concat <$> mapM interpret xs

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
      [ mconcat $ map freeVars (toList (structF (compExprBindings context))),
        mconcat $ map freeVars (toList (structB (compExprBindings context))),
        mconcat $ concatMap (map freeVars . toList) (toList (structU (compExprBindings context))),
        mconcat $ map freeVars (toList (compAssertions context))
      ]

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
    AndU _ x y -> freeVars x <> freeVars y
    OrU _ x y -> freeVars x <> freeVars y
    XorU _ x y -> freeVars x <> freeVars y
    NotU _ x -> freeVars x
    RoLU _ _ x -> freeVars x
    ShLU _ _ x -> freeVars x
    SetU _ x _ y -> freeVars x <> freeVars y
    IfU _ p x y -> freeVars p <> freeVars x <> freeVars y
    BtoU _ x -> freeVars x

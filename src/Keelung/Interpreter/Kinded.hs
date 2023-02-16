{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}

module Keelung.Interpreter.Kinded (run, runAndOutputWitnesses) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bits qualified
import Data.Foldable (toList)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Semiring (Semiring (..))
import GHC.TypeLits (KnownNat)
import Keelung hiding (interpret, run)
import Keelung.Compiler.Syntax.Inputs (Inputs (..))
import Keelung.Data.Bindings
import Keelung.Data.Bindings qualified as Bindings
import Keelung.Data.Struct
import Keelung.Interpreter.Monad
import Keelung.Interpreter.Typed ()
import Keelung.Syntax.Encode.Syntax qualified as Typed

--------------------------------------------------------------------------------

-- | Interpret a program with inputs and return outputs along with the witness
runAndOutputWitnesses :: (GaloisField n, Integral n, Interpret t n) => Elaborated t -> Inputs n -> Either (Error n) ([n], Witness n)
runAndOutputWitnesses (Elaborated expr context) inputs = runM (compHeap context) inputs $ do
  -- interpret assignments of values first
  fs <-
    filterM
      ( \(var, e) -> case e of
          Integer val -> interpret val >>= addF var >> return False
          Rational val -> interpret val >>= addF var >> return False
          _ -> return True
      )
      (IntMap.toList (structF (compExprBindings context)))
  bs <-
    filterM
      ( \(var, e) -> case e of
          Boolean val -> interpret val >>= addB var >> return False
          _ -> return True
      )
      (IntMap.toList (structB (compExprBindings context)))
  us <-
    mapM
      ( \(width, xs) ->
          (width,)
            <$> filterM
              ( \(var, e) -> case e of
                  Typed.ValU _ val -> interpret val >>= addU width var >> return False
                  _ -> return True
              )
              (IntMap.toList xs)
      )
      (IntMap.toList (structU (compExprBindings context)))

  -- interpret the rest of the assignments
  forM_ fs $ \(var, e) -> interpret e >>= addF var
  forM_ bs $ \(var, e) -> interpret e >>= addB var
  forM_ us $ \(width, xs) ->
    forM_ xs $ \(var, e) -> interpret e >>= addU width var

  -- interpret the assertions next
  -- throw error if any assertion fails
  forM_ (compAssertions context) $ \e -> do
    values <- interpret e
    when (values /= [1]) $ do
      bindings <- get
      let bindingsInExpr = Bindings.restrictVars bindings (freeVars e)
      -- collect variables and their bindings in the expression and report them
      throwError $ AssertionError (show e) bindingsInExpr

  -- lastly interpret the expression and return the result
  interpret expr

-- | Interpret a program with inputs.
run :: (GaloisField n, Integral n, Interpret t n) => Elaborated t -> Inputs n -> Either (Error n) [n]
run elab inputs = fst <$> runAndOutputWitnesses elab inputs

--------------------------------------------------------------------------------

instance GaloisField n => Interpret Rational n where
  interpret x = return [fromRational x]

instance (GaloisField n, Integral n) => Interpret Field n where
  interpret val = case val of
    Integer n -> interpret n
    Rational n -> interpret n
    VarF var -> pure <$> lookupF var
    VarFI var -> pure <$> lookupFI var
    VarFP var -> pure <$> lookupFP var
    Add x y -> zipWith (+) <$> interpret x <*> interpret y
    Sub x y -> zipWith (-) <$> interpret x <*> interpret y
    Mul x y -> zipWith (*) <$> interpret x <*> interpret y
    Div x y -> zipWith (/) <$> interpret x <*> interpret y
    IfF p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
    BtoF x -> interpret x

instance (GaloisField n, Integral n) => Interpret Boolean n where
  interpret val = case val of
    Boolean b -> interpret b
    VarB var -> pure <$> lookupB var
    VarBI var -> pure <$> lookupBI var
    VarBP var -> pure <$> lookupBP var
    And x y -> zipWith (*) <$> interpret x <*> interpret y
    Or x y -> zipWith (+) <$> interpret x <*> interpret y
    Xor x y -> zipWith (\x' y' -> x' + y' - 2 * (x' * y')) <$> interpret x <*> interpret y
    Not x -> map (1 -) <$> interpret x
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
    EqU x y -> do
      x' <- interpret x
      y' <- interpret y
      interpret (x' == y')
    BitU x i -> do
      xs <- interpret x
      if Data.Bits.testBit (toInteger (head xs)) i
        then return [one]
        else return [zero]

instance (GaloisField n, Integral n, KnownNat w) => Interpret (UInt w) n where
  interpret val = case val of
    UInt n -> interpret n
    VarU var -> pure <$> lookupU (widthOf val) var
    VarUI var -> pure <$> lookupUI (widthOf val) var
    VarUP var -> pure <$> lookupUP (widthOf val) var
    AddU x y -> zipWith (+) <$> interpret x <*> interpret y
    SubU x y -> zipWith (-) <$> interpret x <*> interpret y
    MulU x y -> zipWith (*) <$> interpret x <*> interpret y
    -- UIntDiv x y -> zipWith (/) <$> interpret x <*> interpret y
    AndU x y -> zipWith bitWiseAnd <$> interpret x <*> interpret y
    OrU x y -> zipWith bitWiseOr <$> interpret x <*> interpret y
    XorU x y -> zipWith bitWiseXor <$> interpret x <*> interpret y
    NotU x -> map bitWiseNot <$> interpret x
    RoLU w n x -> map (bitWiseRotateL w n) <$> interpret x
    ShLU w n x -> map (bitWiseShiftL w n) <$> interpret x
    SetU x i y -> zipWith (\x' y' -> bitWiseSet (widthOf x) x' i y') <$> interpret x <*> interpret y
    IfU p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
    BtoU x -> interpret x

instance GaloisField n => Interpret () n where
  interpret val = case val of
    () -> return []

instance (Interpret t n, GaloisField n) => Interpret [t] n where
  interpret xs = concat <$> mapM interpret xs

instance (GaloisField n, Integral n) => Interpret (ArrM t) n where
  interpret val = case val of
    ArrayRef _elemType _len addr -> do
      heap <- ask
      case IntMap.lookup addr heap of
        Nothing -> error "[ panic ] address not found when trying to read heap"
        Just (elemType, vars) -> case elemType of
          ElemF -> interpret $ map VarF (toList vars)
          ElemB -> interpret $ map VarB (toList vars)
          ElemU width -> mapM (lookupU width) (toList vars)
          ElemArr elemType' len -> concat <$> mapM (interpret . ArrayRef elemType' len) (toList vars)
          EmptyArr -> return []

--------------------------------------------------------------------------------

instance FreeVar Field where
  freeVars expr = case expr of
    Integer _ -> mempty
    Rational _ -> mempty
    VarF var -> updateX (updateF (IntSet.insert var)) mempty
    VarFI var -> updateI (updateF (IntSet.insert var)) mempty
    VarFP var -> updateP (updateF (IntSet.insert var)) mempty
    Add x y -> freeVars x <> freeVars y
    Sub x y -> freeVars x <> freeVars y
    Mul x y -> freeVars x <> freeVars y
    Div x y -> freeVars x <> freeVars y
    IfF x y z -> freeVars x <> freeVars y <> freeVars z
    BtoF x -> freeVars x

instance FreeVar Boolean where
  freeVars expr = case expr of
    Boolean _ -> mempty
    VarB var -> updateX (updateB (IntSet.insert var)) mempty
    VarBI var -> updateI (updateB (IntSet.insert var)) mempty
    VarBP var -> updateP (updateB (IntSet.insert var)) mempty
    And x y -> freeVars x <> freeVars y
    Or x y -> freeVars x <> freeVars y
    Xor x y -> freeVars x <> freeVars y
    Not x -> freeVars x
    EqB x y -> freeVars x <> freeVars y
    EqF x y -> freeVars x <> freeVars y
    EqU x y -> freeVars x <> freeVars y
    IfB x y z -> freeVars x <> freeVars y <> freeVars z
    BitU x _ -> freeVars x

instance KnownNat w => FreeVar (UInt w) where
  freeVars val = case val of
    UInt _ -> mempty
    VarU var -> updateX (updateU (widthOf val) (IntSet.insert var)) mempty
    VarUI var -> updateI (updateU (widthOf val) (IntSet.insert var)) mempty
    VarUP var -> updateP (updateU (widthOf val) (IntSet.insert var)) mempty
    AddU x y -> freeVars x <> freeVars y
    SubU x y -> freeVars x <> freeVars y
    MulU x y -> freeVars x <> freeVars y
    AndU x y -> freeVars x <> freeVars y
    OrU x y -> freeVars x <> freeVars y
    XorU x y -> freeVars x <> freeVars y
    NotU x -> freeVars x
    RoLU _ _ x -> freeVars x
    ShLU _ _ x -> freeVars x
    SetU x _ y -> freeVars x <> freeVars y
    IfU p x y -> freeVars p <> freeVars x <> freeVars y
    BtoU x -> freeVars x

instance FreeVar () where
  freeVars expr = case expr of
    () -> mempty

-- | Collect free variables of an elaborated program
instance FreeVar t => FreeVar (Elaborated t) where
  freeVars (Elaborated value context) = freeVars value <> freeVars context

instance FreeVar Computation where
  freeVars context =
    mconcat
      [ mconcat $ map freeVars (toList (structF (compExprBindings context))),
        mconcat $ map freeVars (toList (structB (compExprBindings context))),
        mconcat $ concatMap (map freeVars . toList) (toList (structU (compExprBindings context))),
        mconcat $ map freeVars (toList (compAssertions context))
      ]

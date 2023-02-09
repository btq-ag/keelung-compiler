{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- Interpreter for Keelung.Syntax.Encode.Syntax
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use lambda-case" #-}

module Keelung.Interpreter.Typed (runAndOutputWitnesses, run) where

import Control.Monad.Except
import Control.Monad.State
import Data.Bits (Bits (..))
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Semiring (Semiring (..))
import Keelung.Compiler.Syntax.Inputs (Inputs)
import Keelung.Data.Bindings
import Keelung.Data.Bindings qualified as Bindings
import Keelung.Data.Struct
import Keelung.Interpreter.Monad
import Keelung.Syntax.Encode.Syntax

--------------------------------------------------------------------------------

-- | Interpret a program with inputs and return outputs along with the witness
runAndOutputWitnesses :: (GaloisField n, Integral n) => Elaborated -> Inputs n -> Either (Error n) ([n], Witness n)
runAndOutputWitnesses (Elaborated expr comp) inputs = runM mempty inputs $ do
  -- interpret assignments of values first
  fs <-
    filterM
      ( \(var, e) -> case e of
          ValF val -> interpret val >>= addF var >> return False
          _ -> return True
      )
      (IntMap.toList (structF (compExprBindings comp)))
  bs <-
    filterM
      ( \(var, e) -> case e of
          ValB val -> interpret val >>= addB var >> return False
          _ -> return True
      )
      (IntMap.toList (structB (compExprBindings comp)))
  us <-
    mapM
      ( \(width, xs) ->
          (width,)
            <$> filterM
              ( \(var, e) -> case e of
                  ValU _ val -> interpret val >>= addU width var >> return False
                  _ -> return True
              )
              (IntMap.toList xs)
      )
      (IntMap.toList (structU (compExprBindings comp)))

  -- interpret the rest of the assignments
  forM_ fs $ \(var, e) -> interpret e >>= addF var
  forM_ bs $ \(var, e) -> interpret e >>= addB var
  forM_ us $ \(width, xs) ->
    forM_ xs $ \(var, e) -> interpret e >>= addU width var

  -- interpret the assertions next
  -- throw error if any assertion fails
  forM_ (compAssertions comp) $ \e -> do
    values <- interpret e
    when (values /= [1]) $ do
      bindings <- get
      let bindingsInExpr = Bindings.restrictVars bindings (freeVars e)
      -- collect variables and their bindings in the expression and report them
      throwError $ AssertionError (show e) bindingsInExpr

  -- lastly interpret the expression and return the result
  interpret expr

-- rawOutputs <- interpret expr

-- case expr of
--   Unit -> return ()
--   Boolean _ -> setBO rawOutputs
--   Field _ -> setFO rawOutputs
--   UInt x -> setUO (widthOfUInt x) rawOutputs
--   Array xs -> case toList xs of
--     [] -> return ()
--     (x : _) -> case x of
--       Boolean _ -> setBO rawOutputs
--       Field _ -> setFO rawOutputs
--       UInt x' -> setUO (widthOfUInt x') rawOutputs
--       _ -> error "impossible"

-- return rawOutputs
-- -- where

--   -- parse the interpreted outputs
--   -- and fill in the bindings of outputs
--   addBindingsOfOutputs :: Expr -> [n] -> M n ()
--   addBindingsOfOutputs expression values = case expression of
--     Unit -> return ()
--     Boolean _ -> addBO values
--     Field _ -> addFO values
--     UInt x -> addUO (widthOfUInt x) values
--     Array xs -> case toList xs of
--       [] -> return ()
--       (x : _) -> case x of
--         Unit -> return ()
--         Boolean _ -> setBO values
--         Field _ -> setFO values
--         UInt x' -> setUO (widthOfUInt x') values
--         Array xs -> _

--   -- Bit width of an UInt
--   widthOfUInt :: UInt -> Width
--   widthOfUInt uint = case uint of
--     ValU w _ -> w
--     VarU w _ -> w
--     VarUI w _ -> w
--     AddU w _ _ -> w
--     SubU w _ _ -> w
--     MulU w _ _ -> w
--     AndU w _ _ -> w
--     OrU w _ _ -> w
--     XorU w _ _ -> w
--     NotU w _ -> w
--     RoLU w _ _ -> w
--     ShLU w _ _ -> w
--     IfU w _ _ _ -> w
--     BtoU w _ -> w

-- | Interpret a program with inputs.
run :: (GaloisField n, Integral n) => Elaborated -> Inputs n -> Either (Error n) [n]
run elab inputs = fst <$> runAndOutputWitnesses elab inputs

--------------------------------------------------------------------------------

instance GaloisField n => Interpret Bool n where
  interpret True = return [one]
  interpret False = return [zero]

instance (GaloisField n, Integral n) => Interpret Boolean n where
  interpret expr = case expr of
    ValB b -> interpret b
    VarB var -> pure <$> lookupB var
    VarBI var -> pure <$> lookupBI var
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
    BitU _ x i -> do
      xs <- interpret x
      if testBit (toInteger (head xs)) i
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
    AddU _ x y -> zipWith (+) <$> interpret x <*> interpret y
    SubU _ x y -> zipWith (-) <$> interpret x <*> interpret y
    MulU _ x y -> zipWith (*) <$> interpret x <*> interpret y
    AndU _ x y -> zipWith bitWiseAnd <$> interpret x <*> interpret y
    OrU _ x y -> zipWith bitWiseOr <$> interpret x <*> interpret y
    XorU _ x y -> zipWith bitWiseXor <$> interpret x <*> interpret y
    NotU _ x -> map bitWiseNot <$> interpret x
    RoLU w i x -> map (bitWiseRotateL w i) <$> interpret x
    ShLU w i x -> map (bitWiseShiftL w i) <$> interpret x
    IfU _ p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
    BtoU _ x -> interpret x

instance (GaloisField n, Integral n) => Interpret Expr n where
  interpret expr = case expr of
    Unit -> return []
    Boolean e -> interpret e
    Field e -> interpret e
    UInt e -> interpret e
    Array xs -> concat <$> mapM interpret xs

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
    VarB var -> updateX (updateB (IntSet.insert var)) mempty
    VarBI var -> updateI (updateB (IntSet.insert var)) mempty
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
    VarF var -> updateX (updateF (IntSet.insert var)) mempty
    VarFI var -> updateI (updateF (IntSet.insert var)) mempty
    AddF x y -> freeVars x <> freeVars y
    SubF x y -> freeVars x <> freeVars y
    MulF x y -> freeVars x <> freeVars y
    DivF x y -> freeVars x <> freeVars y
    IfF p x y -> freeVars p <> freeVars x <> freeVars y
    BtoF x -> freeVars x

instance FreeVar UInt where
  freeVars expr = case expr of
    ValU _ _ -> mempty
    VarU w var -> updateX (updateU w (IntSet.insert var)) mempty
    VarUI w var -> updateI (updateU w (IntSet.insert var)) mempty
    AddU _ x y -> freeVars x <> freeVars y
    SubU _ x y -> freeVars x <> freeVars y
    MulU _ x y -> freeVars x <> freeVars y
    AndU _ x y -> freeVars x <> freeVars y
    OrU _ x y -> freeVars x <> freeVars y
    XorU _ x y -> freeVars x <> freeVars y
    NotU _ x -> freeVars x
    RoLU _ _ x -> freeVars x
    ShLU _ _ x -> freeVars x
    IfU _ p x y -> freeVars p <> freeVars x <> freeVars y
    BtoU _ x -> freeVars x

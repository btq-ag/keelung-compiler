{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- Interpreter for Keelung.Syntax.Typed
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use lambda-case" #-}

module Keelung.Compiler.Interpret.Typed (InterpretError (..), runAndOutputWitnesses, run, runAndCheck) where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bits (Bits (..))
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Semiring (Semiring (..))
import qualified Data.Sequence as Seq
import Data.Serialize (Serialize)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import GHC.Generics (Generic)
import Keelung (N (N))
import qualified Keelung.Compiler.Interpret.Kinded as Kinded
import Keelung.Compiler.Syntax.Inputs (Inputs)
import qualified Keelung.Compiler.Syntax.Inputs as Inputs
import Keelung.Compiler.Util
import Keelung.Data.Bindings
import Keelung.Syntax.Counters
import Keelung.Syntax.Typed
import Keelung.Types

--------------------------------------------------------------------------------

-- | Interpret a program with inputs and return outputs along with the witness
runAndOutputWitnesses :: (GaloisField n, Integral n) => Elaborated -> Inputs n -> Either (InterpretError n) ([n], (IntMap n, IntMap n, IntMap (IntMap n)))
runAndOutputWitnesses (Elaborated expr comp) inputs = runM inputs $ do
  -- interpret assignments of values first
  fs <-
    filterM
      ( \(var, e) -> case e of
          ValF val -> interpret val >>= addF var >> return False
          _ -> return True
      )
      (IntMap.toList (compAssignmentF comp))
  bs <-
    filterM
      ( \(var, e) -> case e of
          ValB val -> interpret val >>= addB var >> return False
          _ -> return True
      )
      (IntMap.toList (compAssignmentB comp))
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
      (IntMap.toList (compAssignmentU comp))

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
      let freeVarsInExpr = freeVars e
      fis <- mapM (\var -> ("$FI" <> show var,) <$> lookupFI var) $ IntSet.toList (ofI $ ofF freeVarsInExpr)
      fs' <- mapM (\var -> ("$F" <> show var,) <$> lookupF var) $ IntSet.toList (ofX $ ofF freeVarsInExpr)
      bis <- mapM (\var -> ("$BI" <> show var,) <$> lookupBI var) $ IntSet.toList (ofI $ ofB freeVarsInExpr)
      bs' <- mapM (\var -> ("$B" <> show var,) <$> lookupB var) $ IntSet.toList (ofX $ ofB freeVarsInExpr)
      us' <-
        concat
          <$> mapM
            ( \(width, bindings) -> do
                is <- mapM (\var -> ("$UI" <> show var,) <$> lookupUI width var) (IntSet.toList (ofI bindings))
                xs <- mapM (\var -> ("$U" <> show var,) <$> lookupU width var) (IntSet.toList (ofX bindings))
                return (is <> xs)
            )
            (IntMap.toList (ofU freeVarsInExpr))
      -- collect variables and their bindings in the expression and report them
      throwError $ InterpretAssertionError e (fis <> fs' <> bis <> bs' <> us')

  -- lastly interpret the expression and return the result
  interpret expr

-- | Interpret a program with inputs.
run :: (GaloisField n, Integral n) => Elaborated -> Inputs n -> Either (InterpretError n) [n]
run elab inputs = fst <$> runAndOutputWitnesses elab inputs

-- | Interpret a program with inputs and run some additional checks.
runAndCheck :: (GaloisField n, Integral n) => Elaborated -> Inputs n -> Either (InterpretError n) [n]
runAndCheck elab inputs = do
  (output, witness) <- runAndOutputWitnesses elab inputs

  -- See if input size is valid
  let expectedInputSize = getCountBySort OfInput (compCounters (elabComp elab))
  let actualInputSize = Inputs.size inputs

  when (expectedInputSize /= actualInputSize) $ do
    throwError $ InterpretInputSizeError expectedInputSize actualInputSize

  -- TODO: restore this check

  -- See if free variables of the program and the witness are the same
  let variables = freeVars elab
  -- traceShowM variables
  -- let varsInWitness = IntMap.keysSet witness
  -- when (variables /= varsInWitness) $ do
  --   let missingInWitness = variables IntSet.\\ varsInWitness
  --   let missingInProgram = IntMap.withoutKeys witness variables
  --   throwError $ InterpretVarUnassignedError missingInWitness missingInProgram

  return output

--------------------------------------------------------------------------------

-- | The interpreter typeclass
class Interpret a n where
  interpret :: a -> M n [n]

instance GaloisField n => Interpret Bool n where
  interpret True = return [one]
  interpret False = return [zero]

instance (GaloisField n, Integral n) => Interpret Boolean n where
  interpret expr = case expr of
    ValB b -> interpret b
    VarB var -> pure <$> lookupB var
    InputVarB var -> pure <$> lookupBI var
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
    InputVarU w var -> pure <$> lookupUI w var
    AddU _ x y -> zipWith (+) <$> interpret x <*> interpret y
    SubU _ x y -> zipWith (-) <$> interpret x <*> interpret y
    MulU _ x y -> zipWith (*) <$> interpret x <*> interpret y
    AndU _ x y -> zipWith bitWiseAnd <$> interpret x <*> interpret y
    OrU _ x y -> zipWith bitWiseOr <$> interpret x <*> interpret y
    XorU _ x y -> zipWith bitWiseXor <$> interpret x <*> interpret y
    NotU _ x -> map bitWiseNot <$> interpret x
    RoLU w i x -> map (Kinded.bitWiseRotateL w i) <$> interpret x
    ShLU w i x -> map (Kinded.bitWiseShiftL w i) <$> interpret x
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

-- Bit x i -> do
--   xs <- interpret x
--   if testBit (toInteger (head xs)) i
--     then return [one]
--     else return [zero]

--------------------------------------------------------------------------------

-- | The interpreter monad
type M2 n = ReaderT (Inputs n) (StateT (Partial n) (Except (InterpretError n)))

runM2 :: Inputs n -> M2 n a -> Either (InterpretError n) (a, Total n)
runM2 inputs p =
  let counters = Inputs.varCounters inputs
      -- construct the initial partial Bindings from Inputs
      initBindings =
        Bindings
          { ofF =
              Binding
                { ofX = Vector.replicate (getCount OfInput OfField counters) Nothing,
                  ofO = Vector.replicate (getCount OfOutput OfField counters) Nothing,
                  ofI = Vector.fromList (map Just (toList (Inputs.numInputs inputs)))
                },
            ofB =
              Binding
                { ofX = Vector.replicate (getCount OfInput OfBoolean counters) Nothing,
                  ofO = Vector.replicate (getCount OfOutput OfBoolean counters) Nothing,
                  ofI = Vector.fromList (map Just (toList (Inputs.boolInputs inputs)))
                },
            ofU =
              IntMap.mapWithKey
                ( \width bindings ->
                    Binding
                      { ofX = Vector.replicate (getCount OfInput (OfUInt width) counters) Nothing,
                        ofO = Vector.replicate (getCount OfOutput (OfUInt width) counters) Nothing,
                        ofI = Vector.fromList (map Just (toList bindings))
                      }
                )
                (Inputs.uintInputs inputs)
          }
   in do
        (result, partialBindings) <- runExcept (runStateT (runReaderT p inputs) initBindings)
        -- make the partial Bindings total
        case toTotal partialBindings of
          Left unbound -> Left (InterpretVarUnassignedError unbound)
          Right bindings -> Right (result, bindings)

addF2 :: Var -> [n] -> M2 n ()
addF2 var vals = modify (updateF (updateX (Vector.// [(var, safeHead vals)])))

addB2 :: Var -> [n] -> M2 n ()
addB2 var vals = modify (updateB (updateX (Vector.// [(var, safeHead vals)])))

addU2 :: Width -> Var -> [n] -> M2 n ()
addU2 w var vals = modify (updateU w (updateX (Vector.// [(var, safeHead vals)])))

lookup' :: (Partial n -> Vector (Maybe a)) -> Int -> M2 n a
lookup' selector var = do
  f <- gets selector
  case f Vector.!? var of
    Nothing -> error "[ panic ] unbound witness index"
    Just Nothing -> error "[ panic ] variable not assigned"
    Just (Just val) -> return val

lookupF2 :: Var -> M2 n n
lookupF2 = lookup' (ofX . ofF)

lookupB2 :: Var -> M2 n n
lookupB2 = lookup' (ofX . ofB)

lookupU2 :: Width -> Var -> M2 n n
lookupU2 w = lookup' (ofX . unsafeLookup w . ofU)
  where
    unsafeLookup x y = case IntMap.lookup x y of
      Nothing -> error "[ panic ] bit width not found"
      Just z -> z

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x : _) = Just x

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = ReaderT (Inputs n) (StateT (IntMap n, IntMap n, IntMap (IntMap n)) (Except (InterpretError n)))

runM :: Inputs n -> M n a -> Either (InterpretError n) (a, (IntMap n, IntMap n, IntMap (IntMap n)))
runM inputs p = runExcept (runStateT (runReaderT p inputs) (mempty, mempty, mempty))

addF :: Var -> [n] -> M n ()
addF var vals = modify (\(f, b, u) -> (IntMap.insert var (head vals) f, b, u))

addB :: Var -> [n] -> M n ()
addB var vals = modify (\(f, b, u) -> (f, IntMap.insert var (head vals) b, u))

addU :: Width -> Var -> [n] -> M n ()
addU w var vals = modify (\(f, b, u) -> (f, b, IntMap.insertWith (<>) w (IntMap.singleton var (head vals)) u))

lookupF :: Show n => Var -> M n n
lookupF var = do
  (fs, _, _) <- get
  case IntMap.lookup var fs of
    Nothing -> throwError $ InterpretUnboundVarError var fs
    Just val -> return val

lookupB :: Show n => Var -> M n n
lookupB var = do
  (_, bs, _) <- get
  case IntMap.lookup var bs of
    Nothing -> throwError $ InterpretUnboundVarError var bs
    Just val -> return val

lookupU :: Show n => Width -> Var -> M n n
lookupU w var = do
  (_, _, us) <- get
  case IntMap.lookup w us of
    Nothing -> error "[ panic ] Wrong bit width"
    Just us' -> case IntMap.lookup var us' of
      Nothing -> throwError $ InterpretUnboundVarError var us'
      Just val -> return val

lookupFI :: Show n => Var -> M n n
lookupFI var = do
  inputs <- asks Inputs.numInputs
  case inputs Seq.!? var of
    Nothing -> throwError $ InterpretUnboundVarError var (IntMap.fromDistinctAscList (zip [0 ..] (toList inputs)))
    Just val -> return val

lookupBI :: Show n => Var -> M n n
lookupBI var = do
  inputs <- asks Inputs.boolInputs
  case inputs Seq.!? var of
    Nothing -> throwError $ InterpretUnboundVarError var (IntMap.fromDistinctAscList (zip [0 ..] (toList inputs)))
    Just val -> return val

lookupUI :: Show n => Int -> Var -> M n n
lookupUI width var = do
  inputss <- asks Inputs.uintInputs
  case IntMap.lookup width inputss of
    Nothing -> error ("lookupUI: no UInt of such bit width: " <> show width)
    Just inputs ->
      case inputs Seq.!? var of
        Nothing -> throwError $ InterpretUnboundVarError var (IntMap.fromDistinctAscList (zip [0 ..] (toList inputs)))
        Just val -> return val

--------------------------------------------------------------------------------

-- | For collecting free variables
class FreeVar a where
  freeVars :: a -> Vars n

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
      [ mconcat $ map freeVars (toList (compAssignmentF context)),
        mconcat $ map freeVars (toList (compAssignmentFI context)),
        mconcat $ map freeVars (toList (compAssignmentB context)),
        mconcat $ map freeVars (toList (compAssignmentBI context)),
        mconcat $ concatMap (map freeVars . toList) (toList (compAssignmentU context)),
        mconcat $ concatMap (map freeVars . toList) (toList (compAssignmentUI context))
      ]

instance FreeVar Boolean where
  freeVars expr = case expr of
    ValB _ -> mempty
    VarB var -> updateF (updateX (IntSet.insert var)) mempty
    InputVarB var -> updateF (updateX (IntSet.insert var)) mempty
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
    VarF var -> updateF (updateI (IntSet.insert var)) mempty
    VarFI var -> updateF (updateI (IntSet.insert var)) mempty
    AddF x y -> freeVars x <> freeVars y
    SubF x y -> freeVars x <> freeVars y
    MulF x y -> freeVars x <> freeVars y
    DivF x y -> freeVars x <> freeVars y
    IfF p x y -> freeVars p <> freeVars x <> freeVars y
    BtoF x -> freeVars x

instance FreeVar UInt where
  freeVars expr = case expr of
    ValU _ _ -> mempty
    VarU w var -> updateU w (updateI (IntSet.insert var)) mempty
    InputVarU w var -> updateU w (updateI (IntSet.insert var)) mempty
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

--------------------------------------------------------------------------------

data InterpretError n
  = InterpretUnboundVarError Var (Witness n)
  | InterpretUnboundAddrError Addr Heap
  | InterpretAssertionError Expr [(String, n)]
  -- | InterpretVarUnassignedError IntSet (Witness n)
  | InterpretInputSizeError Int Int
  | InterpretVarUnassignedError (Vars n)
  deriving (Eq, Generic, NFData)

instance Serialize n => Serialize (InterpretError n)

instance (GaloisField n, Integral n) => Show (InterpretError n) where
  show (InterpretUnboundVarError var witness) =
    "unbound variable $" ++ show var
      ++ " in witness "
      ++ showWitness witness
  show (InterpretUnboundAddrError var heap) =
    "unbound address " ++ show var
      ++ " in heap "
      ++ show heap
  show (InterpretAssertionError expr assignments) =
    "assertion failed: " <> show expr
      <> "\nassignment of variables:\n"
      <> unlines (map (\(var, val) -> "  " <> var <> " := " <> show (N val)) assignments)
  show (InterpretInputSizeError expected actual) =
    "expecting " ++ show expected ++ " inputs but got " ++ show actual
      ++ " inputs"
  show (InterpretVarUnassignedError unboundVariables) =
      "these variables have no bindings:\n  "
            ++ show unboundVariables
    -- ( if IntSet.null missingInWitness
    --     then ""
    --     else
    --       "these variables have no bindings:\n  "
    --         ++ show (IntSet.toList missingInWitness)
    -- )
    --   <> if IntMap.null missingInProgram
    --     then ""
    --     else
    --       "these bindings are not in the program:\n  "
    --         ++ showWitness missingInProgram

--------------------------------------------------------------------------------

bitWiseAnd :: (GaloisField n, Integral n) => n -> n -> n
bitWiseAnd x y = fromInteger $ (Data.Bits..&.) (toInteger x) (toInteger y)

bitWiseOr :: (GaloisField n, Integral n) => n -> n -> n
bitWiseOr x y = fromInteger $ (Data.Bits..|.) (toInteger x) (toInteger y)

bitWiseXor :: (GaloisField n, Integral n) => n -> n -> n
bitWiseXor x y = fromInteger $ Data.Bits.xor (toInteger x) (toInteger y)

bitWiseNot :: (GaloisField n, Integral n) => n -> n
bitWiseNot x = fromInteger $ Data.Bits.complement (toInteger x)

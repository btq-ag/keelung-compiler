{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile (run) where

import Control.Monad
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (foldl'), toList)
import qualified Data.IntMap as IntMap
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq (..))
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Keelung.Compiler.Constraint as Constraint
import Keelung.Compiler.Constraint2
import qualified Keelung.Compiler.Constraint2 as Constraint2
import Keelung.Compiler.Syntax.FieldBits (FieldBits (..))
import Keelung.Compiler.Syntax.Untyped
import Keelung.Syntax.BinRep (BinReps)
import Keelung.Syntax.Counters (Counters, VarType (..), VarSort (..), getCount, addCount)
import Keelung.Syntax.VarCounters

--------------------------------------------------------------------------------

-- | Compile an untyped expression to a constraint system
run :: (GaloisField n, Integral n) => TypeErased n -> Constraint.ConstraintSystem n
run (TypeErased untypedExprs _ countersOld counters relations assertions assignments numBinReps customBinReps) = runM countersOld counters $ do
  forM_ untypedExprs $ \untypedExpr -> do
    case untypedExpr of
      ExprB x -> do
        out <- freshRefBO
        encodeExprB out x
      ExprN x -> do
        out <- freshRefFO
        encodeExprN out x
      ExprU x -> do
        out <- freshRefUO (widthOfU x)
        encodeExprU out x
  

  -- Compile all relations
  encodeRelations relations

  -- Compile assignments to constraints
  mapM_ encodeAssignment assignments

  -- Compile assertions to constraints
  mapM_ encodeAssertion assertions

  constraints <- gets envConstraints

  extraBinReps <- gets envExtraBinReps

  counters' <- gets envVarCounters

  counters'' <- gets envCounters

  return
    ( Constraint.ConstraintSystem
        (Set.map (Constraint2.fromConstraint counters'') constraints)
        numBinReps
        (customBinReps <> extraBinReps)
        counters'
        counters''
    )

-- | Encode the constraint 'out = x'.
encodeAssertion :: (GaloisField n, Integral n) => Expr n -> M n ()
encodeAssertion expr = do
  -- 1 = expr
  case expr of
    ExprB x -> do
      out <- freshRefB
      encodeExprB out x
      add $ cAddB 1 [(out, -1)]
    ExprN x -> do
      out <- freshRefF
      encodeExprN out x
      add $ cAddF 1 [(out, -1)]
    ExprU x -> do
      out <- freshRefU (widthOfU x)
      encodeExprU out x
      add $ cAddU 1 [(out, -1)]

-- | Encode the constraint 'out = expr'.
encodeAssignment :: (GaloisField n, Integral n) => Assignment n -> M n ()
encodeAssignment (AssignmentB ref expr) = encodeExprB ref expr
encodeAssignment (AssignmentN ref expr) = encodeExprN ref expr
encodeAssignment (AssignmentU ref expr) = encodeExprU ref expr

-- encodeRelation :: (GaloisField n, Integral n) => Relation n -> M n ()
-- encodeRelation (Relation bindings assignments assertions) = do
--   forM_ (IntMap.toList bindings) $ \(var, val) -> add $ cadd val [(var, -1)]
--   forM_ (IntMap.toList assignments) $ uncurry encode
--   forM_ assertions $ \expr -> do
--       out <- freshVar
--       encode out expr
--       add $ cadd 1 [(out, -1)] -- 1 = expr

encodeValueBindings :: (GaloisField n, Integral n) => Bindings n -> M n ()
encodeValueBindings bindings = do
  forM_ (Map.toList (bindingsN bindings)) $ \(var, val) -> add $ cAddF val [(var, -1)]
  forM_ (Map.toList (bindingsB bindings)) $ \(var, val) -> add $ cAddB val [(var, -1)]
  forM_ (IntMap.toList (bindingsUs bindings)) $ \(_, bindings') ->
    forM_ (Map.toList bindings') $ \(var, val) -> add $ cAddU val [(var, -1)]

encodeExprBindings :: (GaloisField n, Integral n) => Bindings (Expr n) -> M n ()
encodeExprBindings bindings = do
  forM_ (Map.toList (bindingsN bindings)) $ \(var, ExprN val) -> encodeExprN var val
  forM_ (Map.toList (bindingsB bindings)) $ \(var, ExprB val) -> encodeExprB var val
  forM_ (IntMap.toList (bindingsUs bindings)) $ \(_, bindings') ->
    forM_ (Map.toList bindings') $ \(var, ExprU val) -> encodeExprU var val

encodeRelations :: (GaloisField n, Integral n) => Relations n -> M n ()
encodeRelations (Relations vbs ebs) = do
  encodeValueBindings vbs
  encodeExprBindings ebs

--------------------------------------------------------------------------------

-- | Monad for compilation
data Env n = Env
  { envVarCounters :: VarCounters,
    envCounters :: Counters,
    envConstraints :: Set (Constraint n),
    envExtraBinReps :: BinReps
  }

type M n = State (Env n)

runM :: GaloisField n => VarCounters -> Counters -> M n a -> a
runM varCounters counters program = evalState program (Env varCounters counters mempty mempty)

modifyCounter :: (Counters -> Counters) -> M n ()
modifyCounter f = modify (\env -> env {envCounters = f (envCounters env)})

add :: GaloisField n => [Constraint n] -> M n ()
add cs =
  modify (\env -> env {envConstraints = Set.union (Set.fromList cs) (envConstraints env)})

-- | Adds a new view of binary representation of a variable after rotation.
-- addRotatedBinRep :: Var -> Width -> Var -> Int -> M n ()
-- addRotatedBinRep out width var rotate = do
--   index <- lookupBinRep width var
--   addBinRep $ BinRep out width index rotate
-- addBinRep :: BinRep -> M n ()
-- addBinRep binRep = modify (\env -> env {envExtraBinReps = BinRep.insert binRep (envExtraBinReps env)})

-- freshVar :: M n Var
-- freshVar = do
--   n <- gets (totalVarSize . envVarCounters)
--   modify' (\ctx -> ctx {envVarCounters = bumpIntermediateVar (envVarCounters ctx)})
--   return n

freshRefF :: M n RefF
freshRefF = do
  counters <- gets envCounters
  let index = getCount OfIntermediate OfField counters
  modifyCounter $ addCount OfIntermediate OfField 1
  return $ RefF index

-- fresh :: M n RefB
fresh :: VarSort -> VarType -> (Int -> ref) -> M n ref
fresh sort kind ctor = do
  counters <- gets envCounters
  let index = getCount sort kind counters
  modifyCounter $ addCount sort kind 1
  return $ ctor index

freshRefBO :: M n RefB
freshRefBO = fresh OfOutput OfBoolean RefBO

freshRefFO :: M n RefF
freshRefFO = fresh OfOutput OfField RefFO

freshRefUO :: Width -> M n RefU
freshRefUO width = fresh OfOutput (OfUInt width) (RefUO width)

freshRefB :: M n RefB
freshRefB = do
  counters <- gets envCounters
  let index = getCount OfIntermediate OfBoolean counters
  modifyCounter $ addCount OfIntermediate OfBoolean 1
  return $ RefB index

freshRefU :: Width -> M n RefU
freshRefU width = do
  counters <- gets envCounters
  let index = getCount OfIntermediate (OfUInt width) counters
  modifyCounter $ addCount OfIntermediate (OfUInt width) 1
  return $ RefU width index

-- freshBinRep :: Var -> Int -> M n ()
-- freshBinRep var width
--   | width < 1 = error $ "[ panic ] Cannot create a binary representation of width " <> show width
--   | otherwise = do
--     vars <- replicateM width freshVar
--     addBinRep $ BinRep var width (head vars) 0

-- | Locate the binary representations of some variable
-- lookupBinRep :: Int -> Var -> M n Var
-- lookupBinRep width var = do
--   counters <- gets envVarCounters
--   extraBinReps <- gets envExtraBinReps
--   case lookupBinRepStart counters var of
--     Nothing -> case BinRep.lookup width var extraBinReps of
--       Nothing -> error $ "lookupBinRep: could not find binary representation of " ++ show var
--       Just binRep -> return (binRepBitsIndex binRep)
--     Just index -> return index

getNumberBitWidth :: M n Width
getNumberBitWidth = gets (getNumBitWidth . envVarCounters)

----------------------------------------------------------------

encodeExprB :: (GaloisField n, Integral n) => RefB -> ExprB n -> M n ()
encodeExprB out expr = case expr of
  ValB val -> add $ cAddB val [(out, -1)] -- out = val
  VarB var -> do
    add $ cAddB 0 [(out, 1), (RefB var, -1)] -- out = var
  OutputVarB var -> do
    add $ cAddB 0 [(out, 1), (RefBO var, -1)] -- out = var
  InputVarB var -> do
    add $ cAddB 0 [(out, 1), (RefBI var, -1)] -- out = var
  AndB x0 x1 xs -> do
    a <- wireB x0
    b <- wireB x1
    vars <- mapM wireB xs
    case vars of
      Empty ->
        add $ cMulSimpleB a b out -- out = a * b
      (c :<| Empty) -> do
        aAndb <- freshRefB
        add $ cMulSimpleB a b aAndb -- aAndb = a * b
        add $ cMulSimpleB aAndb c out -- out = aAndb * c
      _ -> do
        -- the number of operands
        let n = 2 + fromIntegral (length vars)
        -- polynomial = n - sum of operands
        let polynomial = (n, (a, -1) : (b, -1) : [(v, -1) | v <- toList vars])
        -- if the answer is 1 then all operands must be 1
        --    (n - sum of operands) * out = 0
        add $
          cMulB
            polynomial
            (0, [(out, 1)])
            (0, [])
        -- if the answer is 0 then not all operands must be 1:
        --    (n - sum of operands) * inv = 1 - out
        inv <- freshRefB
        add $
          cMulB
            polynomial
            (0, [(inv, 1)])
            (1, [(out, -1)])
  OrB x0 x1 xs -> do
    a <- wireB x0
    b <- wireB x1
    vars <- mapM wireB xs
    case vars of
      Empty -> encodeOrB out a b
      (c :<| Empty) -> do
        -- only 3 operands
        aOrb <- freshRefB
        encodeOrB aOrb a b
        encodeOrB out aOrb c
      _ -> do
        -- more than 3 operands, rewrite it as an inequality instead:
        --      if all operands are 0           then 0 else 1
        --  =>  if the sum of operands is 0     then 0 else 1
        --  =>  if the sum of operands is not 0 then 1 else 0
        --  =>  the sum of operands is not 0
        numBitWidth <- getNumberBitWidth
        encodeExprB
          out
          ( NEqN
              (ValN numBitWidth 0)
              ( AddN
                  numBitWidth
                  (BtoN numBitWidth x0)
                  (BtoN numBitWidth x1)
                  (fmap (BtoN numBitWidth) xs)
              )
          )
  XorB x y -> do
    x' <- wireB x
    y' <- wireB y
    encodeXorB out x' y'
  NotB x -> do
    x' <- wireB x
    add $ cAddB 1 [(x', -1), (out, -1)] -- out = 1 - x
  IfB p x y -> do
    p' <- wireB p
    x' <- wireB x
    y' <- wireB y
    encodeIfB out p' x' y'
  NEqB x y -> encodeExprB out (XorB x y)
  NEqN x y -> do
    x' <- wireF x
    y' <- wireF y
    encodeEqualityF False out x' y'
  NEqU x y -> do
    x' <- wireU x
    y' <- wireU y
    encodeEqualityU False out x' y'
  EqB x y -> do
    x' <- wireB x
    y' <- wireB y
    -- Constraint 'x == y = out' ASSUMING x, y are boolean.
    --     x * y + (1 - x) * (1 - y) = out
    -- =>
    --    (1 - x) * (1 - 2y) = (out - y)
    add $
      cMulB
        (1, [(x', -1)])
        (1, [(y', -2)])
        (0, [(out, 1), (y', -1)])
  EqN x y -> do
    x' <- wireF x
    y' <- wireF y
    encodeEqualityF True out x' y'
  EqU x y -> do
    x' <- wireU x
    y' <- wireU y
    encodeEqualityU True out x' y'
  BitU x i -> do
    result <- bitTestU x i
    var <- wireB result
    add $ cAddB 0 [(out, 1), (var, -1)] -- out = var

-- bitTestUOnVar :: (Integral n, GaloisField n) => Width -> Var -> Int -> M n (ExprB n)
-- bitTestUOnVar w var i = do
--   counters <- gets envVarCounters
--   if var < outputVarSize counters
--     then bitTestU (OutputVarU w var) i
--     else do
--       let var' = blendIntermediateVar counters var
--       bitTestU (VarU w var') i

bitTestU :: (Integral n, GaloisField n) => ExprU n -> Int -> M n (ExprB n)
bitTestU expr i = case expr of
  ValU _ val -> return (ValB (testBit val i))
  VarU {} -> error "[ panic ] bitTestU: VarU"
    -- counters <- gets envVarCounters
    -- -- if the index 'i' overflows or underflows, wrap it around
    -- let i' = i `mod` w
    -- let var' = blendIntermediateVar counters var
    -- start <- lookupBinRep w var'
    -- return $ VarB (start + i')
  OutputVarU {} -> error "[ panic ] bitTestU: OutputVarU"
    -- -- if the index 'i' overflows or underflows, wrap it around
    -- let i' = i `mod` w
    -- -- let var' = blendInputVarU counters w var
    -- start <- lookupBinRep w var
    -- -- traceShow ("OutputVarU $" <> show var <> "[" <> show i <> "] => " <> show (start + i')) $ return $ VarB (start + i')
    -- return $ VarB (start + i')
  InputVarU {} -> error "[ panic ] bitTestU: InputVarU"
    -- counters <- gets envVarCounters
    -- -- if the index 'i' overflows or underflows, wrap it around
    -- let i' = i `mod` w
    -- let var' = blendInputVarU counters w var
    -- start <- lookupBinRep w var'
    -- return $ VarB (start + i')
  AndU _ x y xs ->
    AndB
      <$> bitTestU x i
      <*> bitTestU y i
      <*> mapM (`bitTestU` i) xs
  OrU _ x y xs ->
    OrB
      <$> bitTestU x i
      <*> bitTestU y i
      <*> mapM (`bitTestU` i) xs
  XorU _ x y ->
    XorB
      <$> bitTestU x i
      <*> bitTestU y i
  NotU _ x -> NotB <$> bitTestU x i
  _ -> error $ "[ panic ] Unable to perform bitTestU of " <> show expr

encodeExprN :: (GaloisField n, Integral n) => RefF -> ExprN n -> M n ()
encodeExprN out expr = case expr of
  ValN _ val -> add $ cAddF val [(out, -1)] -- out = val
  VarN _ var -> do
    add $ cAddF 0 [(out, 1), (RefF var, -1)] -- out = var
  OutputVarN _ var -> do
    add $ cAddF 0 [(out, 1), (RefFO var, -1)] -- out = var
  InputVarN _ var -> do
    add $ cAddF 0 [(out, 1), (RefFI var, -1)] -- out = var
  SubN _ x y -> do
    x' <- toTermN x
    y' <- toTermN y
    encodeTerms out (x' :<| negateTerm y' :<| Empty)
  AddN _ x y rest -> do
    terms <- mapM toTermN (x :<| y :<| rest)
    encodeTerms out terms
  MulN _ x y -> do
    x' <- wireF x
    y' <- wireF y
    add $ cMulSimpleF x' y' out
  DivN _ x y -> do
    x' <- wireF x
    y' <- wireF y
    add $ cMulSimpleF y' out x'
  IfN _ p x y -> do
    p' <- wireB p
    x' <- wireF x
    y' <- wireF y
    encodeIfF out p' x' y'
  BtoN _ x -> do
    result <- freshRefB
    encodeExprB result x
    add $ cAddF 0 [(out, 1), (RefBtoRefF result, -1)] -- out = var

encodeExprU :: (GaloisField n, Integral n) => RefU -> ExprU n -> M n ()
encodeExprU out expr = case expr of
  ValU _ val -> add $ cAddU val [(out, -1)] -- out = val
  VarU width var -> do
    add $ cAddU 0 [(out, 1), (RefU width var, -1)] -- out = var
  OutputVarU width var -> do
    add $ cAddU 0 [(out, 1), (RefU width var, -1)] -- out = var
  InputVarU width var -> do
    add $ cAddU 0 [(out, 1), (RefU width var, -1)] -- out = var
  SubU w x y -> do
    x' <- wireU x
    y' <- wireU y
    -- freshBinRep out w
    encodeSubU w out x' y'
  AddU w x y -> do
    x' <- wireU x
    y' <- wireU y
    -- freshBinRep out w
    encodeAddU w out x' y'
  MulU w x y -> do
    x' <- wireU x
    y' <- wireU y
    -- freshBinRep out w
    encodeMulU w out x' y'
  AndU w x y xs -> do
    -- freshBinRep out w
    forM_ [0 .. w - 1] $ \i -> do
      encodeExprB
        (RefUBit out i)
        (AndB (BitU x i) (BitU y i) (fmap (`BitU` i) xs))
  OrU w x y xs -> do
    -- freshBinRep out w
    forM_ [0 .. w - 1] $ \i -> do
      encodeExprB
        (RefUBit out i)
        (OrB (BitU x i) (BitU y i) (fmap (`BitU` i) xs))
  -- x' <- bitTestU x i
  -- y' <- bitTestU y i
  -- xs' <- mapM (`bitTestU` i) xs
  -- out' <- bitTestUOnVar w out i >>= wireAsVar . ExprB
  -- encodeExprB out' (OrB x' y' xs')
  XorU w x y -> do
    -- freshBinRep out w
    forM_ [0 .. w - 1] $ \i -> do
      encodeExprB
        (RefUBit out i)
        (XorB (BitU x i) (BitU y i))
  -- x' <- bitTestU x i
  -- y' <- bitTestU y i
  -- out' <- bitTestUOnVar w out i >>= wireAsVar . ExprB
  -- encodeExprB out' (XorB x' y')
  NotU w x -> do
    -- freshBinRep out w
    forM_ [0 .. w - 1] $ \i -> do
      encodeExprB
        (RefUBit out i)
        (NotB (BitU x i))
  -- x' <- bitTestU x i
  -- out' <- bitTestUOnVar w out i >>= wireAsVar . ExprB
  -- encodeExprB out' (NotB x')
  IfU _ p x y -> do
    p' <- wireB p
    x' <- wireU x
    y' <- wireU y
    encodeIfU out p' x' y'
  RoLU {} -> error "[ panic ] encodeExprU: RoLU: not implemented"
  BtoU _ x -> do
    result <- freshRefB
    encodeExprB result x
    add $ cAddU 0 [(out, 1), (RefBtoRefU result, -1)] -- out = var
    -- encodeExprB out x

-- encode :: (GaloisField n, Integral n) => Var -> Expr n -> M n ()
-- encode out expr = case expr of
--   -- values
--   ExprB x -> encodeExprB out x
--   ExprN x -> encodeExprN out x
--   ExprU x -> encodeExprU out x

--------------------------------------------------------------------------------

-- | Pushes the constructor of Rotate inwards
-- encodeRotate :: (GaloisField n, Integral n) => Var -> Int -> ExprU n -> M n ()
-- encodeRotate out i expr = case expr of
--   -- ExprB x -> encode out (ExprB x)
--   -- ExprN x -> case x of
--   --   ValN w n -> do
--   --     n' <- rotateField w n
--   --     encode out (ExprN (ValN w n'))
--   --   VarN w var -> addRotatedBinRep out w var i
--   --   SubN {} -> error "[ panic ] dunno how to compile ROTATE SubN"
--   --   AddN w _ _ _ -> do
--   --     result <- freshVar
--   --     encode result expr
--   --     addRotatedBinRep out w result i
--   --   MulN {} -> error "[ panic ] dunno how to compile ROTATE MulN"
--   --   DivN {} -> error "[ panic ] dunno how to compile ROTATE DivN"
--   --   IfN {} -> error "[ panic ] dunno how to compile ROTATE IfN"
--   --   RoLN {} -> error "[ panic ] dunno how to compile ROTATE RoLN"
--   -- ExprU x -> case x of
--   ValU w n -> do
--     n' <- rotateField w n
--     encode out (ExprU (ValU w n'))
--   VarU w var -> addRotatedBinRep out w var i
--   SubU {} -> error "[ panic ] dunno how to compile ROTATE SubU"
--   AddU w _ _ -> do
--     result <- freshVar
--     encodeExorU result expr
--     addRotatedBinRep out w result i
--   _ -> error "[ panic ] dunno how to compile ROTATE on UInt types"
--   -- Rotate _ n x -> encodeRotate out (i + n) x
--   -- -- NAryOp _ op _ _ _ -> error $ "[ panic ] dunno how to compile ROTATE NAryOp " <> show op
--   where
--     rotateField width n = do
--       let val = toInteger n
--       -- see if we are rotating right (positive) of left (negative)
--       case i `compare` 0 of
--         EQ -> return n -- no rotation
--         -- encode out expr -- no rotation
--         LT -> do
--           let rotateDistance = (-i) `mod` width
--           -- collect the bit values of lower bits that will be rotated to higher bits
--           let lowerBits = [Data.Bits.testBit val j | j <- [0 .. rotateDistance - 1]]
--           -- shift the higher bits left by the rotate distance
--           let higherBits = Data.Bits.shiftR val rotateDistance
--           -- combine the lower bits and the higher bits
--           return $
--             fromInteger $
--               foldl'
--                 (\acc (bit, j) -> if bit then Data.Bits.setBit acc j else acc)
--                 higherBits
--                 (zip lowerBits [width - rotateDistance .. width - 1])

--         -- encode out (Val bw (fromInteger rotatedVal))
--         GT -> do
--           let rotateDistance = i `mod` width
--           -- collect the bit values of higher bits that will be rotated to lower bits
--           let higherBits = [Data.Bits.testBit val j | j <- [width - rotateDistance .. width - 1]]
--           -- shift the lower bits right by the rotate distance
--           let lowerBits = Data.Bits.shiftL val rotateDistance `mod` 2 ^ width
--           -- combine the lower bits and the higher bits
--           return $
--             fromInteger $
--               foldl'
--                 (\acc (bit, j) -> if bit then Data.Bits.setBit acc j else acc)
--                 lowerBits
--                 (zip higherBits [0 .. rotateDistance - 1])

--------------------------------------------------------------------------------

data Term n
  = Constant n -- c
  | WithVars RefF n -- cx

-- Avoid having to introduce new multiplication gates
-- for multiplication by constant scalars.
toTermN :: (GaloisField n, Integral n) => ExprN n -> M n (Term n)
toTermN (MulN _ (ValN _ m) (ValN _ n)) = return $ Constant (m * n)
toTermN (MulN _ (VarN _ var) (ValN _ n)) = return $ WithVars (RefF var) n
toTermN (MulN _ (InputVarN _ var) (ValN _ n)) = return $ WithVars (RefFI var) n
toTermN (MulN _ (OutputVarN _ var) (ValN _ n)) = return $ WithVars (RefFO var) n
toTermN (MulN _ (ValN _ n) (VarN _ var)) = return $ WithVars (RefF var) n
toTermN (MulN _ (ValN _ n) (InputVarN _ var)) = return $ WithVars (RefFI var) n
toTermN (MulN _ (ValN _ n) (OutputVarN _ var)) = return $ WithVars (RefFO var) n
toTermN (MulN _ (ValN _ n) expr) = do
  out <- freshRefF
  encodeExprN out expr
  return $ WithVars out n
toTermN (MulN _ expr (ValN _ n)) = do
  out <- freshRefF
  encodeExprN out expr
  return $ WithVars out n
toTermN (ValN _ n) =
  return $ Constant n
toTermN (VarN _ var) =
  return $ WithVars (RefF var) 1
toTermN (InputVarN _ var) =
  return $ WithVars (RefFI var) 1
toTermN (OutputVarN _ var) =
  return $ WithVars (RefFO var) 1
toTermN expr = do
  out <- freshRefF
  encodeExprN out expr
  return $ WithVars out 1

-- | Negate a Term
negateTerm :: Num n => Term n -> Term n
negateTerm (WithVars var c) = WithVars var (negate c)
negateTerm (Constant c) = Constant (negate c)

encodeTerms :: GaloisField n => RefF -> Seq (Term n) -> M n ()
encodeTerms out terms =
  let (constant, varsWithCoeffs) = foldl' go (0, []) terms
   in add $ cAddF constant $ (out, -1) : varsWithCoeffs
  where
    go :: Num n => (n, [(RefF, n)]) -> Term n -> (n, [(RefF, n)])
    go (constant, pairs) (Constant n) = (constant + n, pairs)
    go (constant, pairs) (WithVars var coeff) = (constant, (var, coeff) : pairs)

-- Given a binary function 'f' that knows how to encode '_⊗_'
-- This functions replaces the occurences of '_⊗_' with 'f' in the following manner:
--      E₀ ⊗ E₁ ⊗ ... ⊗ Eₙ
--  =>
--      E₀ `f` (E₁ `f` ... `f` Eₙ)
-- encodeAndFoldExprs :: (GaloisField n, Integral n) => (Var -> Var -> Var -> M n ()) -> Var -> Expr n -> Expr n -> Seq (Expr n) -> M n ()
-- encodeAndFoldExprs f out x0 x1 xs = do
--   x0' <- wireAsVar x0
--   x1' <- wireAsVar x1
--   vars <- mapM wireAsVar xs
--   go x0' x1' vars
--   where
--     go x y Empty = f out x y
--     go x y (v :<| vs) = do
--       out' <- freshVar
--       go out' v vs
--       f out' x y

-- | If the expression is not already a variable, create a new variable
-- wireAsVar :: (GaloisField n, Integral n) => Expr n -> M n Var
-- wireAsVar (ExprB (VarB var)) = return var
-- wireAsVar (ExprN (VarN _ var)) = return var
-- wireAsVar (ExprU (VarU _ var)) = return var
-- wireAsVar expr = do
--   out <- freshVar
--   encode out expr
--   return out
wireB :: (GaloisField n, Integral n) => ExprB n -> M n RefB
wireB (VarB ref) = return (RefB ref)
wireB (OutputVarB ref) = return (RefBO ref)
wireB (InputVarB ref) = return (RefBI ref)
wireB expr = do
  out <- freshRefB
  encodeExprB out expr
  return out

wireF :: (GaloisField n, Integral n) => ExprN n -> M n RefF
wireF (VarN _ ref) = return (RefF ref)
wireF (OutputVarN _ ref) = return (RefFO ref)
wireF (InputVarN _ ref) = return (RefFI ref)
wireF expr = do
  out <- freshRefF
  encodeExprN out expr
  return out

wireU :: (GaloisField n, Integral n) => ExprU n -> M n RefU
wireU (VarU w ref) = return (RefU w ref)
wireU (OutputVarU w ref) = return (RefUO w ref)
wireU (InputVarU w ref) = return (RefUI w ref)
wireU expr = do
  out <- freshRefU (widthOfU expr)
  encodeExprU out expr
  return out

--------------------------------------------------------------------------------

-- | Equalities are encoded with inequalities and inequalities with CNEQ constraints.
--    Constraint 'x != y = out'
--    The encoding is, for some 'm':
--        1. (x - y) * m = out
--        2. (x - y) * (1 - out) = 0
encodeEqualityU :: (GaloisField n, Integral n) => Bool -> RefB -> RefU -> RefU -> M n ()
encodeEqualityU isEq out x y =
  if x == y
    then do
      -- in this case, the variable x and y happend to be the same
      if isEq
        then encodeExprB out (ValB 1)
        else encodeExprB out (ValB 0)
    else do
      -- introduce a new variable m
      -- if diff = 0 then m = 0 else m = recip diff
      let width = case x of
            RefU w _ -> w
            RefUI w _ -> w
            RefUO w _ -> w
            RefBtoRefU _ -> 1 -- TODO: reexamine this
      m <- freshRefU width

      if isEq
        then do
          --  1. (x - y) * m = 1 - out
          --  2. (x - y) * out = 0
          add $
            cMulU
              (0, [(x, 1), (y, -1)])
              (0, [(m, 1)])
              (1, [(RefBtoRefU out, -1)])
          add $
            cMulU
              (0, [(x, 1), (y, -1)])
              (0, [(RefBtoRefU out, 1)])
              (0, [])
        else do
          --  1. (x - y) * m = out
          --  2. (x - y) * (1 - out) = 0
          add $
            cMulU
              (0, [(x, 1), (y, -1)])
              (0, [(m, 1)])
              (0, [(RefBtoRefU out, 1)])
          add $
            cMulU
              (0, [(x, 1), (y, -1)])
              (1, [(RefBtoRefU out, -1)])
              (0, [])

      --  keep track of the relation between (x - y) and m
      add $ cNEqU x y m

encodeEqualityF :: (GaloisField n, Integral n) => Bool -> RefB -> RefF -> RefF -> M n ()
encodeEqualityF isEq out x y =
  if x == y
    then do
      -- in this case, the variable x and y happend to be the same
      if isEq
        then encodeExprB out (ValB 1)
        else encodeExprB out (ValB 0)
    else do
      -- introduce a new variable m
      -- if diff = 0 then m = 0 else m = recip diff
      m <- freshRefF

      if isEq
        then do
          --  1. (x - y) * m = 1 - out
          --  2. (x - y) * out = 0
          add $
            cMulF
              (0, [(x, 1), (y, -1)])
              (0, [(m, 1)])
              (1, [(RefBtoRefF out, -1)])
          add $
            cMulF
              (0, [(x, 1), (y, -1)])
              (0, [(RefBtoRefF out, 1)])
              (0, [])
        else do
          --  1. (x - y) * m = out
          --  2. (x - y) * (1 - out) = 0
          add $
            cMulF
              (0, [(x, 1), (y, -1)])
              (0, [(m, 1)])
              (0, [(RefBtoRefF out, 1)])
          add $
            cMulF
              (0, [(x, 1), (y, -1)])
              (1, [(RefBtoRefF out, -1)])
              (0, [])

      --  keep track of the relation between (x - y) and m
      add $ cNEqF x y m

--------------------------------------------------------------------------------

-- | Encoding addition on UInts with multiple operands: O(1)
--    C = A + B - 2ⁿ * (Aₙ₋₁ * Bₙ₋₁)
encodeAddOrSubU :: (GaloisField n, Integral n) => Bool -> Width -> RefU -> RefU -> RefU -> M n ()
encodeAddOrSubU isSub width out x y = do
  -- locate the binary representations of the operands
  -- xBinRepStart <- lookupBinRep width x
  -- yBinRepStart <- lookupBinRep width y

  let multiplier = 2 ^ width
  -- We can refactor
  --    out = A + B - 2ⁿ * (Aₙ₋₁ * Bₙ₋₁)
  -- into the form of
  --    (2ⁿ * Aₙ₋₁) * (Bₙ₋₁) = (out - A - B)
  add $
    cMulU
      (0, [(RefBtoRefU (RefUBit x (width - 1)), multiplier)])
      (0, [(RefBtoRefU (RefUBit y (width - 1)), 1)])
      (0, [(out, 1), (x, -1), (y, if isSub then 1 else -1)])

encodeAddU :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
encodeAddU = encodeAddOrSubU False

encodeSubU :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
encodeSubU = encodeAddOrSubU True

-- | Encoding addition on UInts with multiple operands: O(2)
--    C + 2ⁿ * Q = A * B
encodeMulU :: (GaloisField n, Integral n) => Int -> RefU -> RefU -> RefU -> M n ()
encodeMulU width out a b = do
  -- rawProduct = a * b
  rawProduct <- freshRefU width
  add $ cMulSimpleU a b rawProduct
  -- result = rawProduct - 2ⁿ * quotient
  quotient <- freshRefU width
  add $ cAddU 0 [(out, 1), (rawProduct, -1), (quotient, 2 ^ width)]

-- | An universal way of compiling a conditional
encodeIfB :: (GaloisField n, Integral n) => RefB -> RefB -> RefB -> RefB -> M n ()
encodeIfB out p x y = do
  --  out = p * x + (1 - p) * y
  --      =>
  --  (out - x) = (1 - p) * (y - x)
  add $
    cMulB
      (1, [(p, -1)])
      (0, [(x, -1), (y, 1)])
      (0, [(x, -1), (out, 1)])

encodeIfF :: (GaloisField n, Integral n) => RefF -> RefB -> RefF -> RefF -> M n ()
encodeIfF out p x y = do
  --  out = p * x + (1 - p) * y
  --      =>
  --  (out - x) = (1 - p) * (y - x)
  add $
    cMulF
      (1, [(RefBtoRefF p, -1)])
      (0, [(x, -1), (y, 1)])
      (0, [(x, -1), (out, 1)])

encodeIfU :: (GaloisField n, Integral n) => RefU -> RefB -> RefU -> RefU -> M n ()
encodeIfU out p x y = do
  --  out = p * x + (1 - p) * y
  --      =>
  --  (out - x) = (1 - p) * (y - x)
  add $
    cMulU
      (1, [(RefBtoRefU p, -1)])
      (0, [(x, -1), (y, 1)])
      (0, [(x, -1), (out, 1)])

encodeOrB :: (GaloisField n, Integral n) => RefB -> RefB -> RefB -> M n ()
encodeOrB out x y = do
  -- (1 - x) * y = (out - x)
  add $
    cMulB
      (1, [(x, -1)])
      (0, [(y, 1)])
      (0, [(x, -1), (out, 1)])

encodeXorB :: (GaloisField n, Integral n) => RefB -> RefB -> RefB -> M n ()
encodeXorB out x y = do
  -- (1 - 2x) * (y + 1) = (1 + out - 3x)
  add $
    cMulB
      (1, [(x, -2)])
      (1, [(y, 1)])
      (1, [(x, -3), (out, 1)])
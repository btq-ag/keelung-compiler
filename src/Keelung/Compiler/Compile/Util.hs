module Keelung.Compiler.Compile.Util where

import Control.Monad.Except
import Control.Monad.State
import Data.Either (partitionEithers)
import Data.Field.Galois (GaloisField)
import Data.Map.Strict qualified as Map
import Keelung (HasWidth (widthOf))
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Relations.Field (AllRelations)
import Keelung.Compiler.Relations.Field qualified as AllRelations
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintSystem
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Field (FieldType)
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

-- | Monad for compilation
type M n = StateT (ConstraintSystem n) (Except (Error n))

runM :: GaloisField n => (FieldType, Integer, Integer) -> Bool -> Counters -> M n a -> Either (Error n) (ConstraintSystem n)
runM fieldInfo useNewOptimizer counters program =
  runExcept
    ( execStateT
        program
        (ConstraintSystem fieldInfo counters useNewOptimizer mempty mempty mempty mempty AllRelations.new mempty mempty mempty mempty mempty)
    )

modifyCounter :: (Counters -> Counters) -> M n ()
modifyCounter f = modify (\cs -> cs {csCounters = f (csCounters cs)})

freshRefF :: M n RefF
freshRefF = do
  counters <- gets csCounters
  let index = getCount OfIntermediate OfField counters
  modifyCounter $ addCount OfIntermediate OfField 1
  return $ RefFX index

freshRefForU :: Ref -> M n Ref
freshRefForU (F _) = do
  counters <- gets csCounters
  let index = getCount OfIntermediate OfField counters
  modifyCounter $ addCount OfIntermediate OfField 1
  return $ F $ RefFX index
freshRefForU (B _) = do
  counters <- gets csCounters
  let index = getCount OfIntermediate OfBoolean counters
  modifyCounter $ addCount OfIntermediate OfBoolean 1
  return $ B $ RefBX index
freshRefForU (U ref) = do
  let width = widthOf ref
  counters <- gets csCounters
  let index = getCount OfIntermediate (OfUInt width) counters
  modifyCounter $ addCount OfIntermediate (OfUInt width) 1
  return $ U $ RefUX width index

freshRefB :: M n RefB
freshRefB = do
  counters <- gets csCounters
  let index = getCount OfIntermediate OfBoolean counters
  modifyCounter $ addCount OfIntermediate OfBoolean 1
  return $ RefBX index

freshRefU :: Width -> M n RefU
freshRefU width = do
  counters <- gets csCounters
  let index = getCount OfIntermediate (OfUInt width) counters
  modifyCounter $ addCount OfIntermediate (OfUInt width) 1
  return $ RefUX width index

--------------------------------------------------------------------------------

-- | Compile a linear combination of expressions into a polynomial
toPoly :: (GaloisField n, Integral n) => (Expr n -> M n (Either Ref n)) -> (n, [(Expr n, n)]) -> M n (Either n (PolyG Ref n))
toPoly compile (c, xs) = do
  (constants, terms) <- partitionEithers <$> mapM compileTerm xs
  return $ PolyG.build (c + sum constants) terms
  where
    compileTerm (expr, coeff) = do
      result <- compile expr
      case result of
        Left variable -> return $ Right (variable, coeff)
        Right constant -> return $ Left (constant * coeff)

writeMulWithPoly :: (GaloisField n, Integral n) => Either n (PolyG Ref n) -> Either n (PolyG Ref n) -> Either n (PolyG Ref n) -> M n ()
writeMulWithPoly as bs cs = case (as, bs, cs) of
  (Left _, Left _, Left _) -> return ()
  (Left x, Left y, Right zs) ->
    -- z - x * y = 0
    addC [CAddF $ PolyG.addConstant (-x * y) zs]
  (Left x, Right ys, Left z) ->
    -- x * ys = z
    -- x * ys - z = 0
    case PolyG.multiplyBy x ys of
      Left _ -> return ()
      Right poly -> addC [CAddF $ PolyG.addConstant (-z) poly]
  (Left x, Right ys, Right zs) -> do
    -- x * ys = zs
    -- x * ys - zs = 0
    case PolyG.multiplyBy x ys of
      Left c ->
        -- c - zs = 0
        addC [CAddF $ PolyG.addConstant (-c) zs]
      Right ys' -> case PolyG.merge ys' (PolyG.negate zs) of
        Left _ -> return ()
        Right poly -> addC [CAddF poly]
  (Right xs, Left y, Left z) -> writeMulWithPoly (Left y) (Right xs) (Left z)
  (Right xs, Left y, Right zs) -> writeMulWithPoly (Left y) (Right xs) (Right zs)
  (Right xs, Right ys, _) -> addC [CMulF xs ys cs]

writeAddWithPoly :: (GaloisField n, Integral n) => Either n (PolyG Ref n) -> M n ()
writeAddWithPoly xs = case xs of
  Left _ -> return ()
  Right poly -> addC [CAddF poly]

addC :: (GaloisField n, Integral n) => [Constraint n] -> M n ()
addC = mapM_ addOne
  where
    execRelations :: (AllRelations n -> EquivClass.M (Error n) (AllRelations n)) -> M n ()
    execRelations f = do
      cs <- get
      result <- lift $ (EquivClass.runM . f) (csFieldRelations cs)
      case result of
        Nothing -> return ()
        Just relations -> put cs {csFieldRelations = relations}

    -- addBitTestOccurrences :: (GaloisField n, Integral n) => Ref -> Ref -> M n ()
    -- addBitTestOccurrences (B (RefUBit _ refA _)) (B (RefUBit _ refB _)) = do
    --   modify' (\cs -> cs {csBitTests = Map.insertWith (+) refA 1 $ Map.insertWith (+) refB 1 (csBitTests cs)})
    -- addBitTestOccurrences _ _ = return ()

    addBitTestOccurrences' :: (GaloisField n, Integral n) => Ref -> M n ()
    addBitTestOccurrences' (B (RefUBit _ ref _)) = do
      modify' (\cs -> cs {csBitTests = Map.insertWith (+) ref 1 (csBitTests cs)})
    addBitTestOccurrences' _ = return ()

    addOne :: (GaloisField n, Integral n) => Constraint n -> M n ()
    addOne (CAddF xs) = modify' (\cs -> addOccurrences (PolyG.vars xs) $ cs {csAddF = xs : csAddF cs})
    addOne (CVarBindF x c) = do
      execRelations $ AllRelations.assignF x c
    addOne (CVarBindB x c) = do
      addBitTestOccurrences' (B x)
      execRelations $ AllRelations.assignB x c
    addOne (CVarBindU x c) = do
      execRelations $ AllRelations.assignU x c
    addOne (CVarEq x y) = do
      addBitTestOccurrences' x
      addBitTestOccurrences' y
      execRelations $ AllRelations.relateRefs x 1 y 0
    addOne (CVarEqF x y) = do
      execRelations $ AllRelations.relateRefs (F x) 1 (F y) 0
    addOne (CVarEqB x y) = do
      addBitTestOccurrences' (B x)
      addBitTestOccurrences' (B y)
      execRelations $ AllRelations.relateB x (True, y)
    addOne (CVarNEqB x y) = do
      addBitTestOccurrences' (B x)
      addBitTestOccurrences' (B y)
      execRelations $ AllRelations.relateB x (False, y)
    addOne (CVarEqU x y) = do
      execRelations $ AllRelations.assertEqualU x y
    addOne (CMulF x y (Left c)) = modify' (\cs -> addOccurrences (PolyG.vars x) $ addOccurrences (PolyG.vars y) $ cs {csMulF = (x, y, Left c) : csMulF cs})
    addOne (CMulF x y (Right z)) = modify (\cs -> addOccurrences (PolyG.vars x) $ addOccurrences (PolyG.vars y) $ addOccurrences (PolyG.vars z) $ cs {csMulF = (x, y, Right z) : csMulF cs})

--------------------------------------------------------------------------------

writeMul :: (GaloisField n, Integral n) => (n, [(Ref, n)]) -> (n, [(Ref, n)]) -> (n, [(Ref, n)]) -> M n ()
writeMul as bs cs = writeMulWithPoly (uncurry PolyG.build as) (uncurry PolyG.build bs) (uncurry PolyG.build cs)

writeAdd :: (GaloisField n, Integral n) => n -> [(Ref, n)] -> M n ()
writeAdd c as = writeAddWithPoly (PolyG.build c as)

writeValF :: (GaloisField n, Integral n) => RefF -> n -> M n ()
writeValF a x = addC [CVarBindF (F a) x]

writeValB :: (GaloisField n, Integral n) => RefB -> Bool -> M n ()
writeValB a x = addC [CVarBindB a x]

writeValU :: (GaloisField n, Integral n) => RefU -> n -> M n ()
writeValU a x = addC [CVarBindU a x]

writeEqB :: (GaloisField n, Integral n) => RefB -> RefB -> M n ()
writeEqB a b = addC [CVarEqB a b]

writeNEqB :: (GaloisField n, Integral n) => RefB -> RefB -> M n ()
writeNEqB a b = addC [CVarNEqB a b]

writeEqU :: (GaloisField n, Integral n) => RefU -> RefU -> M n ()
writeEqU a b = addC [CVarEqU a b]

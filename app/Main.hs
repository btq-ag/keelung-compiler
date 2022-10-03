{-# LANGUAGE DataKinds #-}

module Main where

import qualified AggregateSignature.Program as AggSig
import AggregateSignature.Util
import Control.Arrow (left)
import Control.Monad
import Control.Monad.Except
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BS
import Data.Field.Galois (GaloisField)
import Data.Serialize (Serialize, decode, encode)
import Encode (asJSONLines)
import Keelung (elaborate)
import Keelung.Compiler
  ( ConstraintSystem,
    Error (..),
    compile,
    compileO0Elab,
    compileO1Elab,
    compileO2Elab,
    interpretElab,
    numberOfConstraints,
    toR1CS,
  )
import Keelung.Constraint.R1CS (R1CS)
import Keelung.Field
import Keelung.Syntax.Typed hiding (elaborate)
import Main.Utf8 (withUtf8)
import Option

main :: IO ()
main = withUtf8 $ do
  options <- getOptions
  case options of
    Protocol CompileO0 -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> do
          case fieldType of
            B64 -> output (asB64 $ compileO0Elab elaborated)
            GF181 -> output (asGF181 $ compileO0Elab elaborated)
            BN128 -> output (asBN128 $ compileO0Elab elaborated)
    Protocol CompileO1 -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> do
          case fieldType of
            B64 -> output (asB64 $ compileO1Elab elaborated)
            GF181 -> output (asGF181 $ compileO1Elab elaborated)
            BN128 -> output (asBN128 $ compileO1Elab elaborated)
    Protocol CompileO2 -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> do
          case fieldType of
            B64 -> output (asB64 $ compileO2Elab elaborated)
            GF181 -> output (asGF181 $ compileO2Elab elaborated)
            BN128 -> output (asBN128 $ compileO2Elab elaborated)
    Protocol Interpret -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated, [Integer])
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated, inputs) -> do
          case fieldType of
            B64 -> putStrLn $ BSC.unpack $ encode (interpretElab elaborated (map fromInteger inputs) :: Either String [B64])
            GF181 -> putStrLn $ BSC.unpack $ encode (interpretElab elaborated (map fromInteger inputs) :: Either String [GF181])
            BN128 -> putStrLn $ BSC.unpack $ encode (interpretElab elaborated (map fromInteger inputs) :: Either String [BN128])
    Protocol ToJSON -> do
      blob <- getContents
      let decoded = decode (BSC.pack blob) :: Either String (FieldType, Elaborated)
      case decoded of
        Left err -> print err
        Right (fieldType, elaborated) -> do
          case fieldType of
            B64 -> outputAndwriteJSONLines (asB64 $ compileO1Elab elaborated)
            GF181 -> outputAndwriteJSONLines (asGF181 $ compileO1Elab elaborated)
            BN128 -> outputAndwriteJSONLines (asBN128 $ compileO1Elab elaborated)
    Version -> putStrLn "Keelung v0.5.1"
  where
    asB64 :: Either (Error B64) (ConstraintSystem B64) -> Either (Error B64) (ConstraintSystem B64)
    asB64 = id 

    asGF181 :: Either (Error GF181) (ConstraintSystem GF181) -> Either (Error GF181) (ConstraintSystem GF181)
    asGF181 = id

    asBN128 :: Either (Error BN128) (ConstraintSystem BN128) -> Either (Error BN128) (ConstraintSystem BN128)
    asBN128 = id

    output :: (Serialize n, GaloisField n, Integral n) => Either (Error n) (ConstraintSystem n) -> IO ()
    output cs = putStrLn $ BSC.unpack $ encode (left show (toR1CS <$> cs))

    outputAndwriteJSONLines :: (Serialize n, GaloisField n, Integral n) => Either (Error n) (ConstraintSystem n) -> IO ()
    outputAndwriteJSONLines cs = do 
      output cs 
      case cs of 
        Left err -> print err 
        Right cs' -> do
          let r1cs = toR1CS cs'
          BS.writeFile "out.jsonl" (asJSONLines r1cs)

-- putStrLn $ BSC.unpack $ encode (left show (toR1CS

-- Profile dimension numOfSigs -> profile dimension numOfSigs
-- Count dimension numOfSigs -> do
--   putStrLn $ show dimension ++ ":" ++ show numOfSigs
--   -- snarklConstraints dimension numOfSigs
--   -- keelung dimension numOfSigs
--   keelungConstraints dimension numOfSigs

run :: (GaloisField n, Integral n) => ExceptT (Error n) IO () -> IO ()
run f = do
  res <- runExceptT f
  case res of
    Left err -> print err
    Right () -> return ()

--------------------------------------------------------------------------------

profile :: Int -> Int -> IO ()
profile dimension numOfSigs = run $ do
  let settings =
        Settings
          { enableAggChecking = True,
            enableSizeChecking = True,
            enableLengthChecking = True
          }
  let param = makeParam dimension numOfSigs 42 settings :: Param GF181

  -- compile & optimize
  -- erased <- liftEither $ erase (aggregateSignature setup)
  -- liftIO $ do
  --   print ("erasedExpr", Untyped.sizeOfExpr <$> erasedExpr erased)
  --   print ("erasedAssertions", length $ erasedAssertions erased, sum $ map Untyped.sizeOfExpr (erasedAssertions erased))
  --   print ("erasedAssignments", length $ erasedAssignments erased, sum $ map (\(Untyped.Assignment _ expr) -> Untyped.sizeOfExpr expr) (erasedAssignments erased))
  --   print ("erasedNumOfVars", erasedNumOfVars erased)
  --   print ("erasedInputVars size", IntSet.size $ erasedInputVars erased)
  --   print ("erasedBooleanVars size", IntSet.size $ erasedBooleanVars erased)

  -- print ("compNextVar", compNextVar computed)
  -- print ("compNextAddr", compNextAddr computed)
  -- print ("compInputVars", IntSet.size $ compInputVars computed)
  -- print ("compHeap", IntMap.size $ compHeap computed)
  -- print ("compNumAsgns", length $ compNumAsgns computed, sum $ map (\(Assignment _ expr) -> sizeOfExpr expr) (compNumAsgns computed))
  -- print ("compBoolAsgns", length $ compBoolAsgns computed, sum $ map (\(Assignment _ expr) -> sizeOfExpr expr) (compBoolAsgns computed))
  -- print ("compAssertions", length $ compAssertions computed, sum $ map sizeOfExpr (compAssertions computed))

  -- compile & optimize
  aggSig <- liftEither $ compile (AggSig.aggregateSignature param)
  liftIO $
    print (numberOfConstraints (aggSig :: ConstraintSystem GF181))

-- for examing the number of constraints generated by Keelung
-- keelungConstraints :: Int -> Int -> IO ()
-- keelungConstraints dimension numOfSigs = run $ do
--   let settings =
--         Settings
--           { enableAggChecking = True,
--             enableSizeChecking = True,
--             enableLengthChecking = True
--           }
--   let param = makeParam dimension numOfSigs 42 settings :: Param GF181

--   checkAgg <-
--     liftEither $
--       compile $
--         AggSig.checkAgg $
--           makeParam dimension numOfSigs 42 (Settings True False False)
--   let checkAgg' = Optimizer.optimize2 $ Optimizer.optimize checkAgg :: ConstraintSystem GF181

--   checkSize <-
--     liftEither $
--       compile $
--         AggSig.checkSize $
--           makeParam dimension numOfSigs 42 (Settings False True False)
--   let checkSize' = Optimizer.optimize2 $ Optimizer.optimize checkSize :: ConstraintSystem GF181

--   checkLength <-
--     liftEither $
--       compile $
--         AggSig.checkLength $
--           makeParam dimension numOfSigs 42 (Settings False False True)
--   let checkLength' = Optimizer.optimize2 $ Optimizer.optimize checkLength :: ConstraintSystem GF181

--   aggSig <- liftEither $ compile (AggSig.aggregateSignature param)
--   let aggSig' = Optimizer.optimize2 $ Optimizer.optimize aggSig :: ConstraintSystem GF181

--   liftIO $ putStrLn "  Keelung: "
--   liftIO $
--     putStrLn $
--       "    not optimized:      "
--         ++ show (numberOfConstraints aggSig)
--         ++ " ( "
--         ++ show (numberOfConstraints checkAgg)
--         ++ " / "
--         ++ show (numberOfConstraints checkSize)
--         ++ " / "
--         ++ show (numberOfConstraints checkLength)
--         ++ " )"
--   liftIO $
--     putStrLn $
--       "    optimized:          "
--         ++ show (numberOfConstraints aggSig')
--         ++ " ( "
--         ++ show (numberOfConstraints checkAgg')
--         ++ " / "
--         ++ show (numberOfConstraints checkSize')
--         ++ " / "
--         ++ show (numberOfConstraints checkLength')
--         ++ " )"

-- liftIO $
--   putStrLn $
--     "    patially evaluated: "
--       ++ show (numberOfConstraints aggSig''))
--       ++ " ( "
--       ++ show (numberOfConstraints checkAgg''))
--       ++ " / "
--       ++ show (numberOfConstraints checkSize''))
--       ++ " / "
--       ++ show (numberOfConstraints checkLength''))
--       ++ " )"

-- for examing the number of constraints generated by Snarkl
-- snarklConstraints :: Int -> Int -> IO ()
-- snarklConstraints dimension numOfSigs = run $ do
--   do
--     -- not optimized

--     let count =
--           show . Set.size . Snarkl.cs_constraints
--             . Snarkl.compile
--             . Snarkl.elaborate

--     liftIO $ putStrLn "  Snarkl: "
--     liftIO $
--       putStrLn $
--         "    not optimized: "
--           ++ count checkAgg
--           ++ " / "
--           ++ count checkSize
--           ++ " / "
--           ++ count checkLength
--           ++ " / "
--           ++ count aggSig

--   do
--     -- optimized
--     let count =
--           show . Set.size . Snarkl.cs_constraints . snd
--             . Snarkl.simplifyConstrantSystem False mempty
--             . Snarkl.compile
--             . Snarkl.elaborate

--     liftIO $
--       putStrLn $
--         "    optimized: "
--           ++ count checkAgg
--           ++ " / "
--           ++ count checkSize
--           ++ " / "
--           ++ count checkLength
--           ++ " / "
--           ++ count aggSig
--   where
--     checkAgg :: Snarkl.Comp 'Snarkl.TBool GF181
--     checkAgg = Snarkl.checkAgg $ makeParam dimension numOfSigs 42 $ Settings True False False

--     checkSize :: Snarkl.Comp 'Snarkl.TBool GF181
--     checkSize = Snarkl.checkSize $ makeParam dimension numOfSigs 42 $ Settings False True False

--     checkLength :: Snarkl.Comp 'Snarkl.TBool GF181
--     checkLength = Snarkl.checkLength $ makeParam dimension numOfSigs 42 $ Settings False False True

--     aggSig :: Snarkl.Comp 'Snarkl.TBool GF181
--     aggSig = Snarkl.aggregateSignature $ makeParam dimension numOfSigs 42 $ Settings True True True

-- for examing the complexity of expression generated after elaboration
keelungElaborate :: IO ()
keelungElaborate = do
  forM_ [2 :: Int .. 7] $ \i -> do
    let dimension = 2 ^ i
    let numOfSigs = 4
    let param = makeParam dimension numOfSigs 42 settings :: Param GF181

    let result = elaborate (AggSig.aggregateSignature param)
    case result of
      Left err -> print err
      Right elaborated -> do
        print
          ( sizeOfExpr (elabExpr elaborated),
            length (compNumAsgns (elabComp elaborated)),
            length (compBoolAsgns (elabComp elaborated)),
            compNextVar (elabComp elaborated)
          )
  where
    -- run (2 ^ i) 4

    settings :: Settings
    settings =
      Settings
        { enableAggChecking = True,
          enableSizeChecking = True,
          enableLengthChecking = True
        }
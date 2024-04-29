{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Experiment (run, tests) where

import Control.Monad (forM_)
import Data.Either qualified as Either
import Data.Field.Galois (Prime)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Word (Word8)
import Keelung hiding (MulU, VarUI)
import Keelung.Compiler (Error (..))
import Keelung.Compiler.Compile.Error (Error)
import Keelung.Data.LC qualified as LC
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice (Slice))
import Keelung.Data.SlicePolynomial (SlicePoly)
import Keelung.Data.SlicePolynomial qualified as SlicePoly
import Keelung.Data.SlicePolynomial qualified as SlicePolynomial
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Interpreter qualified as Interpreter
import Keelung.Solver qualified as Solver
import Test.Arbitrary (arbitraryUOfWidth)
import Test.Hspec
import Test.QuickCheck
import Test.Util

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

mergeRefMap :: (Integral n) => Map Ref n -> Map Ref n -> Map Ref n
mergeRefMap xs ys = Map.filter (/= 0) (Map.unionWith (+) xs ys)

tests :: SpecWith ()
tests = describe "Experiment" $ do
  describe "merge" $ do
    it "should result in valid PolyL" $ do
      let convert x = case x of
            Left _ -> error "should not happen"
            Right xs -> xs
      let poly1 = convert $ PolyL.new 0 [] [(Slice (RefUX 32 0) 0 30, 8)]
      let poly2 = convert $ PolyL.new 0 [] [(Slice (RefUX 32 1) 10 20, 10), (Slice (RefUX 32 0) 0 30, 9)]
      case PolyL.merge poly1 (poly2 :: PolyL (Prime 17)) of
        Left constant' -> do
          constant' `shouldBe` PolyL.polyConstant poly1 + PolyL.polyConstant poly2
        Right polynomial -> do
          PolyL.polyConstant polynomial `shouldBe` PolyL.polyConstant poly1 + PolyL.polyConstant poly2
          print (SlicePoly.fromSlices (PolyL.toSlices polynomial))
          SlicePoly.fromSlices (PolyL.toSlices polynomial) `shouldBe` SlicePoly.fromSlices (PolyL.toSlices poly1) <> SlicePoly.fromSlices (PolyL.toSlices poly2)
          PolyL.polyRefs polynomial `shouldBe` PolyL.polyRefs poly1 `mergeRefMap` PolyL.polyRefs poly2
          PolyL.validate polynomial `shouldBe` Nothing

-- property $ \(poly1, poly2) -> do
--   case PolyL.merge poly1 (poly2 :: PolyL (Prime 17)) of
--     Left constant' -> do
--       constant' `shouldBe` PolyL.polyConstant poly1 + PolyL.polyConstant poly2
--     Right polynomial -> do
--       PolyL.polyConstant polynomial `shouldBe` PolyL.polyConstant poly1 + PolyL.polyConstant poly2
--       SlicePoly.fromSlices (PolyL.toSlices polynomial) `shouldBe` SlicePoly.fromSlices (PolyL.toSlices poly1) <> SlicePoly.fromSlices (PolyL.toSlices poly2)
--       PolyL.polyRefs polynomial `shouldBe` PolyL.polyRefs poly1 `mergeRefMap` PolyL.polyRefs poly2
--       PolyL.validate polynomial `shouldBe` Nothing
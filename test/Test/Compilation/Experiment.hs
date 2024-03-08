{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment (run, tests) where

import Data.Field.Galois (Prime)
import Data.Map (Map)
import Data.Map qualified as Map
import Keelung (widthOf)
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Slice (Slice)
import Test.Arbitrary ()
import Test.Hspec
import qualified Keelung.Data.Slice as Slice
import Keelung.Data.Reference

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

toSliceMap :: (Integral n) => [(Slice, n)] -> Map Slice n
toSliceMap = Map.filterWithKey (\slice n -> widthOf slice /= 0 && n /= 0) . Map.fromListWith (+)

mergeSliceMap :: (Integral n) => Map Slice n -> Map Slice n -> Map Slice n
mergeSliceMap xs ys = Map.filterWithKey (\slice n -> widthOf slice /= 0 && n /= 0) (Map.unionWith (+) xs ys)

tests :: SpecWith ()
tests =
  describe "insertSlices" $ do
    -- it "should result in valid PolyL" $ do
    --   property $ \(slice1, slice2, poly) -> do
    --     case PolyL.insertSlices [slice1, slice2] poly of
    --       Left constant' -> do
    --         constant' `shouldBe` PolyL.polyConstant poly
    --         null (toSliceMap [slice1, slice2]) && null (PolyL.polyRefs poly) `shouldBe` True
    --       Right polynomial -> do
    --         toSliceMap (PolyL.toSlices (polynomial :: PolyL (Prime 17)))
    --           `shouldBe` toSliceMap (PolyL.toSlices poly) `mergeSliceMap` toSliceMap [slice1, slice2]

    it "should result in valid PolyL" $ do
      let slice2 = (Slice.Slice (RefUI 22 10) 3 7, 7)
      let poly = case PolyL.new 9 [] [(Slice.Slice (RefUI 22 10) 6 10, 1)] of 
                    Left _ -> error "nope"
                    Right p -> p
      -- property $ \(poly) -> do
      case PolyL.insertSlices [slice2] poly of
        Left constant' -> do
          constant' `shouldBe` PolyL.polyConstant poly
          null (toSliceMap [slice2]) && null (PolyL.polyRefs poly) `shouldBe` True
        Right polynomial -> do
          print $ toSliceMap (PolyL.toSlices poly) 
          print $ toSliceMap [ slice2]
          toSliceMap (PolyL.toSlices (polynomial :: PolyL (Prime 17)))
            `shouldBe` toSliceMap (PolyL.toSlices poly) `mergeSliceMap` toSliceMap [ slice2]


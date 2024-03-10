{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment (run, tests) where

import Data.Field.Galois (Prime)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Test.Arbitrary ()
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

-- toSliceMap :: (Integral n) => [(Slice, n)] -> Map Slice n
-- toSliceMap = Map.filterWithKey (\slice n -> widthOf slice /= 0 && n /= 0) . Map.fromListWith (+)

-- mergeSliceMap :: (Integral n) => Map Slice n -> Map Slice n -> Map Slice n
-- mergeSliceMap xs ys = Map.filterWithKey (\slice n -> widthOf slice /= 0 && n /= 0) (Map.unionWith (+) xs ys)

-- toLimbMap :: (Integral n) => [(Limb, n)] -> Map Limb n
-- toLimbMap = Map.filterWithKey (\limb n -> not (Limb.null limb) && n /= 0) . Map.fromListWith (+)

tests :: SpecWith ()
tests =
  describe "fromLimbs" $ do
    --  (P (15 `modulo` 17),[({$UI₁₄5[6] + ... + 2⁶$UI₁₄5[12]},P (12 `modulo` 17)),({$UI₁₄5[5] + ... + 2²$UI₁₄5[7]},P (6 `modulo` 17))])
    let constant = 15
    let limbs = [(Limb.new (RefUI 14 5) 7 6 (Left True), 12), (Limb.new (RefUI 14 5) 3 5 (Left True), 6)]
    it "should result in valid PolyL" $ do
      case PolyL.fromLimbs constant limbs of
        Left _ -> return ()
        Right poly -> do
          -- PolyL.polyConstant poly `shouldBe` constant
          -- PolyL.polyLimbs poly `shouldBe` toLimbMap limbs
          PolyL.validate (poly :: PolyL (Prime 17)) `shouldBe` Nothing

-- describe "insertSlices" $ do
--   -- it "should result in valid PolyL" $ do
--   --   property $ \(slice1, slice2, poly) -> do
--   --     case PolyL.insertSlices [slice1, slice2] poly of
--   --       Left constant' -> do
--   --         constant' `shouldBe` PolyL.polyConstant poly
--   --         null (toSliceMap [slice1, slice2]) && null (PolyL.polyRefs poly) `shouldBe` True
--   --       Right polynomial -> do
--   --         toSliceMap (PolyL.toSlices (polynomial :: PolyL (Prime 17)))
--   --           `shouldBe` toSliceMap (PolyL.toSlices poly) `mergeSliceMap` toSliceMap [slice1, slice2]

--   it "should result in valid PolyL" $ do
--     let slice2 = (Slice.Slice (RefUI 22 10) 3 7, 7)
--     let poly = case PolyL.new 9 [] [(Slice.Slice (RefUI 22 10) 6 10, 1)] of
--                   Left _ -> error "nope"
--                   Right p -> p
--     -- property $ \(poly) -> do
--     case PolyL.insertSlices [slice2] poly of
--       Left constant' -> do
--         constant' `shouldBe` PolyL.polyConstant poly
--         null (toSliceMap [slice2]) && null (PolyL.polyRefs poly) `shouldBe` True
--       Right polynomial -> do
--         print $ toSliceMap (PolyL.toSlices poly)
--         print $ toSliceMap [ slice2]
--         toSliceMap (PolyL.toSlices (polynomial :: PolyL (Prime 17)))
--           `shouldBe` toSliceMap (PolyL.toSlices poly) `mergeSliceMap` toSliceMap [ slice2]

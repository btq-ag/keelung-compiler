module Test.FieldRelations (tests, run) where

import Control.Monad.Except
import Control.Monad.State
import Keelung hiding (run)
import Keelung.Compiler.Compile.Relations.FieldRelations (FieldRelations)
import Keelung.Compiler.Compile.Relations.FieldRelations qualified as FieldRelations
import Keelung.Compiler.Constraint
import Test.Hspec (SpecWith, describe, hspec, it)
import Test.Hspec.Expectations.Lifted

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "FieldRelations" $ do
    it "Relate ($0 = $1)" $
      runM $ do
        RefFX 0 `relate` (1, RefFX 1, 0)

        assertRelation (RefFX 0) 1 (RefFX 1) 0
        assertRelation (RefFX 1) 1 (RefFX 0) 0

    it "Relate ($0 = 2$1)" $
      runM $ do
        RefFX 0 `relate` (2, RefFX 1, 0) -- x = 2y
        assertRelation (RefFX 0) 2 (RefFX 1) 0
        assertRelation (RefFX 0) 1 (RefFX 0) 0
        assertRelation (RefFX 1) (1 / 2) (RefFX 0) 0
        assertRelation (RefFX 1) 1 (RefFX 1) 0

    it "Relate ($0 = 2$1 + 1)" $
      runM $ do
        RefFX 0 `relate` (2, RefFX 1, 1) -- x = 2y + 1
        assertRelation (RefFX 0) 2 (RefFX 1) 1
        assertRelation (RefFX 1) (1 / 2) (RefFX 0) (-1 / 2) -- y = 1/2x - 1/2
    it "Relate (x = 2y + 1 & y = 3z + 2)" $
      runM $ do
        RefFX 0 `relate` (2, RefFX 1, 1) -- x = 2y + 1
        RefFX 1 `relate` (3, RefFX 2, 2) -- y = 3z + 2

        -- x = 2y + 1
        assertRelation (RefFX 0) 2 (RefFX 1) 1
        -- y = 1/2x - 1/2
        assertRelation (RefFX 1) (1 / 2) (RefFX 0) (-1 / 2)
        -- x = 6z + 5
        assertRelation (RefFX 0) 6 (RefFX 2) 5
        -- z = 1/6x - 5/6
        assertRelation (RefFX 2) (1 / 6) (RefFX 0) (-5 / 6)
        -- y = 3z + 2
        assertRelation (RefFX 1) 3 (RefFX 2) 2
        -- z = 1/3y - 2/3
        assertRelation (RefFX 2) (1 / 3) (RefFX 1) (-2 / 3)

type M = StateT (FieldRelations GF181) IO

runM :: M a -> IO a
runM p = evalStateT p FieldRelations.new

relate :: RefT -> (GF181, RefT, GF181) -> M ()
relate var (slope, val, intercept) = do
  xs <- get
  case runExcept (FieldRelations.relateRef (F var) (slope, F val, intercept) xs) of
    Left err -> error $ show err
    Right Nothing -> return ()
    Right (Just result) -> put result

-- | Assert that `var1 = slope * var2 + intercept`
assertRelation :: RefT -> GF181 -> RefT -> GF181 -> M ()
assertRelation var1 slope var2 intercept = do
  xs <- get
  FieldRelations.relationBetween (F var1) (F var2) xs `shouldBe` Just (slope, intercept)

------------------------------------------------------------------------

-- instance (Arbitrary n, GaloisField n) => Arbitrary (FieldRelations n) where
--   arbitrary = do
--     relations <- Arbitrary.vector 100

--     return $ foldl go FieldRelations.new relations
--     where
--       go xs (var, slope, ref, intercept) = Maybe.fromMaybe xs (FieldRelations.relate var (slope, ref, intercept) xs)
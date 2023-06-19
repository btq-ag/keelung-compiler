module Test.PolyG () where

-- import Control.Monad.State
-- import Data.Map.Strict qualified as Map
-- import Data.Maybe qualified as Maybe
-- import Keelung
-- import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind)
-- import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
-- import Test.Hspec (SpecWith, describe, hspec, it)
-- import Test.Hspec.Expectations.Lifted
-- import Test.QuickCheck (Arbitrary (arbitrary))
-- import Test.QuickCheck.Arbitrary qualified as Arbitrary

-- run :: IO ()
-- run = hspec tests

-- tests :: SpecWith ()
-- tests = do
--   describe "PolyG" $ do
--     it "substPolyG" $
--       property $ \setup -> do

-- import Control.Monad
-- import Data.Map.Strict (Map)
-- import Data.Map.Strict qualified as Map
-- import Data.Maybe qualified as Maybe
-- import Data.Set (Set)
-- import Data.Set qualified as Set
-- import Data.Traversable (for)
-- import Keelung hiding (compile)
-- import Keelung.Compiler.Constraint (RefB (..), RefF (..), substPolyG)
-- import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind)
-- import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
-- import Keelung.Data.PolyG (PolyG)
-- import Keelung.Data.PolyG qualified as PolyG
-- import Test.Hspec
-- import Test.QuickCheck hiding ((.&.))

-- run :: IO ()
-- run = hspec tests

-- tests :: SpecWith ()
-- tests = do
--   describe "PolyG" $ do
--     it "substPolyG" $
--       property $ \setup -> do

--         -- traverse _ (1, 'a')


--         -- substPolyG (setupPolyGs setup) (setupUnionFind setup) `shouldBe` setupPolyGs setup
--         let substituted = flip map (setupPolyGs setup) $ \polynomial -> do
--               case substPolyG (setupUnionFind setup) polynomial of
--                 Nothing -> polynomial
--                 Just (polynomial', _) -> polynomial'
--         let substituted' = flip map substituted $ \polynomial -> do
--               case substPolyG (setupUnionFind setup) polynomial of
--                 Nothing -> polynomial
--                 Just (polynomial', _) -> polynomial'
--         --  Maybe (PolyG ref n, UnionFind ref n, [ref])
--         -- UnionFind ref n -> PolyG ref n -> Maybe (PolyG ref n, UnionFind ref n, [ref])

--         -- run Basic.identity [inp :: GF181] [inp]
--         -- print (setup :: Setup RefF (N GF181))
--         print (substituted' :: [PolyG RefF (N GF181)])

-- data Setup var n = Setup
--   { setupPinnedVarSet :: Set var,
--     setupIntemediateVarSet :: Set var,
--     setupUnionFind :: UnionFind var n,
--     setupPolyGs :: [PolyG var n],
--     setupAssignments :: Map var n
--   }
--   deriving (Show)

-- instance Arbitrary RefF where
--   arbitrary =
--     oneof
--       [ RefFO <$> chooseInt (0, 99),
--         RefFI <$> chooseInt (0, 99),
--         RefF <$> chooseInt (0, 99)
--         -- RefB <$> arbitrary
--       ]



-- instance Arbitrary RefB where
--   arbitrary =
--     oneof
--       [ RefBO <$> chooseInt (0, 99),
--         RefBI <$> chooseInt (0, 99),
--         RefB <$> chooseInt (0, 99)
--         -- do
--         --   width <- chooseInt (1, 99)
--         --   index <- chooseInt (0, width - 1)
--         --   RefUBit width <$> arbitrary <*> pure index
--       ]

-- -- instance Arbitrary RefUX where
-- --   arbitrary =
-- --     oneof
-- --       [ RefUO <$> arbitrary <*> arbitrary,
-- --         RefUI <$> arbitrary <*> arbitrary,
-- --         RefUX <$> arbitrary <*> arbitrary,
-- --         RefBtoRefUX <$> arbitrary
-- --       ]

-- instance (Arbitrary var, Arbitrary n, GaloisField n, Ord var) => Arbitrary (Setup var n) where
--   arbitrary = do
--     -- generate a set of pinned variables
--     pinnedVarList <- vector 10

--     -- generate a set of intermediate variables
--     intermediateVarList <- vector 100

--     let mixedVarList = pinnedVarList ++ intermediateVarList

--     -- generate a list of relations for all intermediate variables for constructing a UnionFind
--     relations <- forM intermediateVarList $ \var -> do
--       root <- elements pinnedVarList
--       slope <- choose (1, 99)
--       intercept <- choose (0, 99)
--       pure (var, slope, root, intercept)
--     let unionFind = foldl buildUnionFind UnionFind.new relations

--     -- generate a list of PolyGs
--     polyGs <- replicateM 100 (genPolyG mixedVarList)

--     assignments <- forM pinnedVarList $ \var -> do
--       n <- choose (0, 99)
--       pure (var, n)

--     return $ Setup (Set.fromList pinnedVarList) (Set.fromList intermediateVarList) unionFind polyGs (Map.fromList assignments)
--     where
--       buildUnionFind xs (var, slope, ref, intercept) = Maybe.fromMaybe xs (UnionFind.relate var (slope, ref, intercept) xs)
--       genPolyG varList = do
--         -- number of variables in the polynomial
--         size <- chooseInt (1, 1)
--         xs <- replicateM size $ do
--           var <- elements varList
--           n <- choose (0, 99)
--           return (var, n)
--         constant <- choose (0, 99)
--         case PolyG.build constant xs of
--           Left _ -> genPolyG varList
--           Right polyG -> pure polyG
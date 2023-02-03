module Test.PolyG (run, tests) where

import Control.Monad
import Data.Maybe qualified as Maybe
import Data.Set (Set)
import Data.Set qualified as Set
import Keelung hiding (compile, run)
import Keelung.Compiler.Constraint (RefB (..), RefF (..), substPolyG2)
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind)
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Test.Hspec
import Test.QuickCheck hiding ((.&.))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "PolyG" $ do
    it "substPolyG" $
      property $ \setup -> do
        -- substPolyG (setupPolyGs setup) (setupUnionFind setup) `shouldBe` setupPolyGs setup
        -- forM_ (setupPolyGs setup) $ \polynomial -> do 
        --   case substPolyG2 (setupUnionFind setup) polynomial of 
        --     Nothing -> pure ()
            -- Just 
            --  Maybe (PolyG ref n, UnionFind ref n, [ref])
        -- UnionFind ref n -> PolyG ref n -> Maybe (PolyG ref n, UnionFind ref n, [ref])

        -- run Basic.identity [inp :: GF181] [inp]
        print (setup :: Setup RefF (N GF181))

data Setup var n = Setup
  { setupVarSet :: Set var,
    setupUnionFind :: UnionFind var n,
    setupPolyGs :: [PolyG var n],
    setupAssignments :: Map var n
  }
  deriving (Show)

instance Arbitrary RefF where
  arbitrary =
    oneof
      [ RefFO <$> chooseInt (0, 99),
        RefFI <$> chooseInt (0, 99),
        RefF <$> chooseInt (0, 99),
        RefBtoRefF <$> arbitrary
      ]

instance Arbitrary RefB where
  arbitrary =
    oneof
      [ RefBO <$> chooseInt (0, 99),
        RefBI <$> chooseInt (0, 99),
        RefB <$> chooseInt (0, 99)
        -- do
        --   width <- chooseInt (1, 99)
        --   index <- chooseInt (0, width - 1)
        --   RefUBit width <$> arbitrary <*> pure index
      ]

-- instance Arbitrary RefU where
--   arbitrary =
--     oneof
--       [ RefUO <$> arbitrary <*> arbitrary,
--         RefUI <$> arbitrary <*> arbitrary,
--         RefU <$> arbitrary <*> arbitrary,
--         RefBtoRefU <$> arbitrary
--       ]

instance (Arbitrary var, Arbitrary n, GaloisField n, Ord var) => Arbitrary (Setup var n) where
  arbitrary = do
    -- generate a set of variables
    varList <- vector 100

    -- generate a list of relations for constructing a UnionFind
    relations <- replicateM 100 $ do
      var <- elements varList
      root <- elements varList
      slope <- choose (1, 99)
      intercept <- choose (0, 99)
      pure (var, slope, root, intercept)
    let unionFind = foldl buildUnionFind UnionFind.new relations

    -- generate a list of PolyGs
    polyGs <- replicateM 100 (genPolyG varList)

    assignments <- forM varList $ \var -> do
      n <- choose (0, 99)
      pure (var, n)

    return $ Setup (Set.fromList varList) unionFind polyGs (Map.fromList assignments)
    where
      buildUnionFind xs (var, slope, ref, intercept) = Maybe.fromMaybe xs (UnionFind.relate var (slope, ref, intercept) xs)
      genPolyG varList = do
        -- number of variables in the polynomial
        size <- chooseInt (1, 10)
        xs <- replicateM size $ do
          var <- elements varList
          n <- choose (0, 99)
          return (var, n)
        constant <- choose (0, 99)
        case PolyG.build constant xs of
          Left _ -> genPolyG varList
          Right polyG -> pure polyG
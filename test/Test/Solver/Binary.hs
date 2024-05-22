{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Test.Solver.Binary (tests, run) where

import Data.Field.Galois
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Maybe qualified as Maybe
import Keelung (Var)
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Solver.Binary qualified as Binary
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Binary" $ do
  return ()
  -- describe "satisfiable" $ do
  --   it "test" $ do
  --     -- Satisfiable B 0b1110001 + B 0b10111111$0 + B 0b111111$1 + B 0b11100101$2 + B 0b10010100$3 + B 0b1001110$4 (fromList [(0,False),(1,False),(2,True),(3,True),(4,False)])

  --     let polynomial = case Poly.buildEither 0b1110001 [(0, 0b10111111), (1, 0b111111), (2, 0b11100101), (3, 0b10010100), (4, 0b1001110)] of
  --           Left _ -> error "Poly.buildEither"
  --           Right p -> p :: Poly (Binary 283)
  --         assignments = IntMap.fromList [(0, False), (1, False), (2, True), (3, True), (4, False)]
  --     let actual = Binary.run polynomial
  --     case actual of
  --       Nothing -> fail "No solution found"
  --       Just result -> satisfies assignments result `shouldBe` True

-- it "Binary 283" $ do
--   property $ \(Satisfiable polynomial assignments) -> do
--     let actual = Binary.run (polynomial :: Poly (Binary 283))
--     case actual of
--       Nothing -> fail "No solution found"
--       Just result -> satisfies assignments result `shouldBe` True

-- describe "other cases" $ do
--   it "$0 = 0" $ do
--     let polynomial = case Poly.buildEither 0 [(0, 1)] of
--           Left _ -> error "Poly.buildEither"
--           Right p -> p :: Poly (Binary 283)
--     let actual = Binary.run polynomial
--     let expected = Just $ Binary.Result (IntMap.fromList [(0, False)]) mempty mempty
--     actual `shouldBe` expected

--   it "$0 = 1" $ do
--     let polynomial = case Poly.buildEither 1 [(0, 1)] of
--           Left _ -> error "Poly.buildEither"
--           Right p -> p :: Poly (Binary 283)
--     let actual = Binary.run polynomial
--     let expected = Just $ Binary.Result (IntMap.fromList [(0, True)]) mempty mempty
--     actual `shouldBe` expected

--   it "$0 + 2$1 = 1" $ do
--     let polynomial = case Poly.buildEither 1 [(0, 1), (1, 2)] of
--           Left _ -> error "Poly.buildEither"
--           Right p -> p :: Poly (Binary 283)
--     let actual = Binary.run polynomial
--     let expected = Just $ Binary.Result (IntMap.fromList [(0, True), (1, False)]) mempty mempty
--     actual `shouldBe` expected

--   it "$0 + $1 = 1" $ do
--     let polynomial = case Poly.buildEither 1 [(0, 1), (1, 1)] of
--           Left _ -> error "Poly.buildEither"
--           Right p -> p :: Poly (Binary 283)
--     let actual = Binary.run polynomial
--     let expected = Just $ Binary.Result mempty [(IntSet.fromList [0], IntSet.fromList [1])] mempty
--     actual `shouldBe` expected

--   it "$0 + $1 = 2" $ do
--     let polynomial = case Poly.buildEither 2 [(0, 1), (1, 1)] of
--           Left _ -> error "Poly.buildEither"
--           Right p -> p :: Poly (Binary 283)
--     let actual = Binary.run polynomial
--     let expected = Nothing
--     actual `shouldBe` expected

--   it "$0 + $1 + 2$2 = 2" $ do
--     let polynomial = case Poly.buildEither 2 [(0, 1), (1, 1), (2, 2)] of
--           Left _ -> error "Poly.buildEither"
--           Right p -> p :: Poly (Binary 283)
--     let actual = Binary.run polynomial
--     let expected = Just $ Binary.Result (IntMap.fromList [(2, True)]) [(IntSet.fromList [0, 1], mempty)] mempty
--     actual `shouldBe` expected

-------------------------------------------------------------------------------

instance (GaloisField n, Arbitrary n) => Arbitrary (TestCase n) where
  arbitrary = do
    numberOfTerms <- choose (1, 5)
    coefficients <- vectorOf numberOfTerms (arbitrary `suchThat` (> 0)) :: Gen [n]

    assignments <- vectorOf numberOfTerms arbitrary
    let constant = sum $ zipWith (\coeff val -> if val then coeff else 0) coefficients assignments
    let polynomial = case Poly.buildEither constant (zip [0 ..] coefficients) of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly n
    pure $ Satisfiable polynomial (IntMap.fromDistinctAscList $ zip [0 ..] assignments)

data TestCase n = Satisfiable (Poly n) (IntMap Bool)
  deriving (Show)

-- | An assignment satisfies the result if it's a model of the polynomial
satisfies :: IntMap Bool -> Binary.Result -> Bool
satisfies expected (Binary.Result actual equivClass relations) =
  let difference = IntMap.difference expected actual <> IntMap.difference actual expected
      intersection = IntMap.intersectionWith (==) expected actual
   in ( and intersection -- see if the intersected assignments are equal
          && ( IntMap.null difference -- see if the difference is empty
                 || ( satisfiesEquivClass difference -- see if the difference satisfies the equiv class
                        && satisfiesRelations difference -- see if the difference satisfies the relations
                    )
             )
      )
  where
    satisfiesEquivClass :: IntMap Bool -> Bool
    satisfiesEquivClass = Maybe.isJust . IntMap.foldrWithKey step (Just IntMap.empty)
      where
        step :: Var -> Bool -> Maybe (IntMap Bool) -> Maybe (IntMap Bool)
        step _ _ Nothing = Nothing -- failed
        step root val (Just known) = case findEquivClass root equivClass of
          Nothing -> Just known
          Just (sameSign, oppositeSign) -> Just $ IntSet.fold (`IntMap.insert` not val) (IntSet.fold (`IntMap.insert` val) known sameSign) oppositeSign

    findEquivClass :: Var -> [(IntSet, IntSet)] -> Maybe (IntSet, IntSet)
    findEquivClass var = foldr step Nothing
      where
        step :: (IntSet, IntSet) -> Maybe (IntSet, IntSet) -> Maybe (IntSet, IntSet)
        step _ (Just acc) = Just acc
        step (sameSign, oppositeSign) Nothing
          | IntSet.member var sameSign = Just (sameSign, oppositeSign)
          | IntSet.member var oppositeSign = Just (oppositeSign, sameSign)
          | otherwise = Nothing

    satisfiesRelation :: IntMap Bool -> (Bool, IntSet) -> Bool
    satisfiesRelation xs (parity, vars) =
      parity
        == foldr
          ( \var acc -> case IntMap.lookup var xs of
              Nothing -> error "[ panic ] Variables in relations not in model"
              Just val -> if val then not acc else acc
          )
          True
          (IntSet.toList vars)

    satisfiesRelations :: IntMap Bool -> Bool
    satisfiesRelations xs = all (satisfiesRelation xs) relations
{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use list comprehension" #-}
{-# HLINT ignore "Redundant if" #-}

module Test.Solver.Binary (tests, run, satisfies) where

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
  describe "satisfiable" $ do
    it "Binary 283" $ do
      property $ \(Satisfiable polynomial assignments) -> do
        let actual = Binary.run (polynomial :: Poly (Binary 283))
        case actual of
          Nothing -> fail "No solution found"
          Just result -> validate assignments result `shouldBe` []

-------------------------------------------------------------------------------

instance (GaloisField n, Arbitrary n) => Arbitrary (TestCase n) where
  arbitrary = do
    numberOfTerms <- choose (1, 40)
    coefficients <- vectorOf numberOfTerms (arbitrary `suchThat` (> 0)) :: Gen [n]

    assignments <- vectorOf numberOfTerms arbitrary
    let constant = sum $ zipWith (\coeff val -> if val then coeff else 0) coefficients assignments
    let polynomial = case Poly.buildEither constant (zip [0 ..] coefficients) of
          Left _ -> error "Poly.buildEither"
          Right p -> p :: Poly n
    pure $ Satisfiable polynomial (IntMap.fromDistinctAscList $ zip [0 ..] assignments)

data TestCase n = Satisfiable (Poly n) (IntMap Bool)
  deriving (Show)

data Error
  = ConflictingAssignments (IntMap Bool) -- conflicting assignments
  | EquivClassNotSatisfied (IntMap Bool) -- actual assignments
  | RelationNotSatisfied
      (IntMap Bool) -- expected assignments
      (IntMap Bool) -- actual assignments
      [Binary.PolyB] -- remaining relations
  deriving (Eq)

instance Show Error where
  show (ConflictingAssignments assignments) = "Conflicts between the solved assignments and the expected answer: " <> show assignments
  show (EquivClassNotSatisfied assignments) = "[ panic ] Solved assignments that conflicts with UnionFind: " <> show assignments
  show (RelationNotSatisfied expected solved relations) =
    "????:\n  expected assigmnents: "
      <> show (IntMap.toList expected)
      <> "\n  solved assignments:"
      <> show (IntMap.toList solved)
      <> "\n  remaining relations:"
      <> show relations

-- | An assignment satisfies the result if it's a model of the polynomial
validate :: IntMap Bool -> Binary.Result -> [Error]
validate expected (Binary.Result actual equivClass _relations) =
  let difference = IntMap.difference expected actual <> IntMap.difference actual expected
      intersection = IntMap.intersectionWith (==) expected actual
   in if and intersection
        then
          if IntMap.null difference
            then []
            else
              if satisfiesEquivClass difference
                then []
                else -- case unsatisfiedRelations difference of
                -- [] -> []
                -- unsatisfied -> [RelationNotSatisfied expected actual unsatisfied]
                  [EquivClassNotSatisfied actual]
        else [ConflictingAssignments difference]
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

-- satisfiesRelation :: IntMap Bool -> Binary.PolyB -> Bool
-- satisfiesRelation xs (Binary.PolyB vars parity) =
--   parity
--     == foldr
--       ( \var acc -> case IntMap.lookup var xs of
--           Nothing -> error "[ panic ] Variables in relations not in model"
--           Just val -> if val then not acc else acc
--       )
--       True
--       (IntSet.toList vars)

-- unsatisfiedRelations :: IntMap Bool -> [Binary.PolyB]
-- unsatisfiedRelations xs = filter (not . satisfiesRelation xs) (Set.toList relations)

-- | An assignment satisfies the result if it's a model of the polynomial
satisfies :: IntMap Bool -> Binary.Result -> Bool
satisfies expected = null . validate expected
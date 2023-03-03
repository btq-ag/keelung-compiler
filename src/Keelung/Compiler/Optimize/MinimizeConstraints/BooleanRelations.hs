{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.Optimize.MinimizeConstraints.BooleanRelations
  ( BooleanRelations,
    Relation (..),
    new,
    lookup,
    bindToValue,
    relate,
    exportPinnedBitTests,
    size,
    relationBetween,
  )
where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung.Compiler.Constraint (RefB (..), RefU)
import Keelung.Syntax (Width)
import Prelude hiding (lookup)

data BooleanRelations n = BooleanRelations
  { links :: Map RefB (Either (n, RefB) n),
    sizes :: Map RefB Int,
    -- | Here stores bit tests on pinned UInt variables, so that we can export them as constraints later.
    pinnedBitTests :: Set (Width, RefU, Int)
  }
  deriving (Eq, Generic, NFData)

instance (Show n, Eq n, Num n) => Show (BooleanRelations n) where
  show xs =
    "BooleanRelations {\n"
      ++ "  sizes = "
      ++ showList' (map (\(var, n) -> show var <> ": " <> show n) (Map.toList $ sizes xs))
      ++ "\n\n"
      ++ "  pinnedBitTests = " <> show (Set.toList (exportPinnedBitTests xs)) <> "\n\n"
      ++ mconcat (map showLink (Map.toList $ links xs))
      ++ "\n}"
    where
      showList' ys = "[" <> List.intercalate ", " ys <> "]"

      showLink (var, Left (slope, root)) = "  " <> show var <> " = " <> (if slope == 1 then "" else show slope) <> show root <> "\n"
      showLink (var, Right intercept) = "  " <> show var <> " = " <> show intercept <> "\n"

new :: BooleanRelations n
new = BooleanRelations mempty mempty mempty

data Relation n = Root | Constant n | ChildOf n RefB

-- | Returns 'Nothing' if the variable is already a root.
--   else returns 'Just (slope, root)'  where 'var = slope * root + intercept'
lookup :: Num n => BooleanRelations n -> RefB -> Relation n
lookup xs var = case Map.lookup var (links xs) of
  Nothing -> Root -- var is a root
  Just (Right intercept) -> Constant intercept -- var is a root
  Just (Left (slope, parent)) -> case lookup xs parent of
    Root -> ChildOf slope parent
    Constant intercept' ->
      -- parent is a value
      -- var = slope * parent + intercept
      -- parent = intercept'
      --  =>
      -- var = slope * intercept' + intercept
      Constant (slope * intercept')
    ChildOf slope' grandparent ->
      -- var = slope * parent + intercept
      -- parent = slope' * grandparent + intercept'
      --  =>
      -- var = slope * (slope' * grandparent + intercept') + intercept
      --  =>
      -- var = slope * slope' * grandparent + slope * intercept' + intercept
      ChildOf (slope * slope') grandparent

-- | Calculates the relation between two variables `var1` and `var2`
--   Returns `Nothing` if the two variables are not related.
--   Returns `Just (slope, intercept)` where `var1 = slope * var2 + intercept` if the two variables are related.
relationBetween :: GaloisField n => RefB -> RefB -> BooleanRelations n -> Maybe n
relationBetween var1 var2 xs = case (lookup xs var1, lookup xs var2) of
  (Root, Root) ->
    if var1 == var2
      then Just 1
      else Nothing -- var1 and var2 are roots, but not the same one
  (Root, ChildOf slope2 root2) ->
    -- var2 = slope2 * root2 + intercept2
    --  =>
    -- root2 = (var2 - intercept2) / slope2
    if var1 == root2
      then -- var1 = root2
      --  =>
      -- var1 = (var2 - intercept2) / slope2
        Just (recip slope2)
      else Nothing
  (Root, Constant _) -> Nothing -- var1 is a root, var2 is a value
  (ChildOf slope1 root1, Root) ->
    -- var1 = slope1 * root1 + intercept1
    if var2 == root1
      then -- var2 = root1
      --  =>
      -- var1 = slope1 * var2 + intercept1
        Just slope1
      else Nothing
  (Constant _, Root) -> Nothing -- var1 is a value, var2 is a root
  (ChildOf slope1 root1, ChildOf slope2 root2) ->
    -- var1 = slope1 * root1 + intercept1
    -- var2 = slope2 * root2 + intercept2
    if root1 == root2
      then -- var2 = slope2 * root2 + intercept2
      --  =>
      -- root2 = (var2 - intercept2) / slope2 = root1
      --  =>
      -- var1 = slope1 * root1 + intercept1
      --  =>
      -- var1 = slope1 * ((var2 - intercept2) / slope2) + intercept1
      --  =>
      -- var1 = slope1 * var2 / slope2 - slope1 * intercept2 / slope2 + intercept1
        Just (slope1 / slope2)
      else Nothing
  (Constant _, ChildOf _ _) -> Nothing -- var1 is a value
  (ChildOf _ _, Constant _) -> Nothing -- var2 is a value
  (Constant _, Constant _) -> Nothing -- both are values

-- | If the RefB is of RefUBit, remember it
rememberPinnedBitTest :: RefB -> BooleanRelations n -> BooleanRelations n
rememberPinnedBitTest (RefUBit width ref index) xs = xs {pinnedBitTests = Set.insert (width, ref, index) (pinnedBitTests xs)}
rememberPinnedBitTest _ xs = xs

-- | Bind a variable to a value
bindToValue :: GaloisField n => RefB -> n -> BooleanRelations n -> BooleanRelations n
bindToValue x value xs =
  case lookup xs x of
    Root ->
      -- x does not have a parent, so it is its own root
      rememberPinnedBitTest x $
        xs
          { links = Map.insert x (Right value) (links xs),
            sizes = Map.insert x 1 (sizes xs)
          }
    Constant _oldValue ->
      -- x is already a root with `_oldValue` as its value
      -- TODO: handle this kind of conflict in the future
      -- FOR NOW: overwrite the value of x with the new value
      rememberPinnedBitTest x $
        xs
          { links = Map.insert x (Right value) (links xs)
          }
    ChildOf slopeP parent ->
      -- x is a child of `parent` with slope `slopeP` and intercept `interceptP`
      --  x = slopeP * parent + interceptP
      -- now since that x = value, we have
      --  value = slopeP * parent + interceptP
      -- =>
      --  value - interceptP = slopeP * parent
      -- =>
      --  parent = (value - interceptP) / slopeP
      rememberPinnedBitTest x $
        xs
          { links =
              Map.insert parent (Right (value / slopeP)) $
                Map.insert x (Right value) $
                  links xs,
            sizes = Map.insert x 1 (sizes xs)
          }

relate :: GaloisField n => RefB -> (n, RefB) -> BooleanRelations n -> Maybe (BooleanRelations n)
relate x (0, _) xs = Just $ bindToValue x 0 xs
relate x (slope, y) xs
  | x > y = relate' x (slope, y) xs -- x = slope * y + intercept
  | x < y = relate' y (recip slope, x) xs -- y = x / slope - intercept / slope
  | otherwise = Nothing

-- | Establish the relation of 'x = slope * y + intercept'
--   Returns Nothing if the relation has already been established
relate' :: GaloisField n => RefB -> (n, RefB) -> BooleanRelations n -> Maybe (BooleanRelations n)
relate' x (slope, y) xs =
  case lookup xs x of
    Constant interceptX ->
      -- x is already a root with `interceptX` as its value
      --  x = slope * y + intercept
      --  x = interceptX
      -- =>
      --  slope * y + intercept = interceptX
      -- =>
      --  y = (interceptX - intercept) / slope
      Just $ bindToValue y interceptX xs
    ChildOf slopeX rootOfX ->
      -- x is a child of `rootOfX` with slope `slopeX` and intercept `interceptX`
      --  x = slopeX * rootOfX + interceptX
      --  x = slope * y + intercept
      -- =>
      --  slopeX * rootOfX + interceptX = slope * y + intercept
      -- =>
      --  slopeX * rootOfX = slope * y + intercept - interceptX
      -- =>
      --  rootOfX = (slope * y + intercept - interceptX) / slopeX
      relate rootOfX (slope / slopeX, y) xs
    Root ->
      -- x does not have a parent, so it is its own root
      case lookup xs y of
        Constant interceptY ->
          -- y is already a root with `interceptY` as its value
          --  x = slope * y + intercept
          --  y = interceptY
          -- =>
          --  x = slope * interceptY + intercept
          Just $ bindToValue x (slope * interceptY) xs
        ChildOf slopeY rootOfY ->
          -- y is a child of `rootOfY` with slope `slopeY` and intercept `interceptY`
          --  y = slopeY * rootOfY + interceptY
          --  x = slope * y + intercept
          -- =>
          --  x = slope * (slopeY * rootOfY + interceptY) + intercept
          -- =>
          --  x = slope * slopeY * rootOfY + slope * interceptY + intercept
          Just $
            rememberPinnedBitTest x $
              xs
                { links = Map.insert x (Left (slope * slopeY, rootOfY)) (links xs),
                  sizes = Map.insertWith (+) y 1 (sizes xs)
                }
        Root ->
          -- y does not have a parent, so it is its own root
          Just $
            rememberPinnedBitTest x $
              xs
                { links = Map.insert x (Left (slope, y)) (links xs),
                  sizes = Map.insertWith (+) y 1 (sizes xs)
                }

size :: BooleanRelations n -> Int
size = Map.size . links

exportPinnedBitTests :: BooleanRelations n -> Set RefB
exportPinnedBitTests = Set.map (\(w, ref, i) -> RefUBit w ref i) . pinnedBitTests
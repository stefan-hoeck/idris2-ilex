module Set

import Data.List.Quantifiers
import Data.Vect
import Hedgehog
import Text.ILex.Char.Set

%default total

sets : Gen Set
sets = rangeSet <$> list (linear 0 10) rngs
  where
    rng : Gen Range
    rng =
      (\[x,y] => range (min x y) (max x y)) <$> hlist [anyBits32, anyBits32]

    rngs : Gen Range
    rngs = frequency [(1, pure Empty), (20, rng)]

prop_unionAssociative : Property
prop_unionAssociative =
  property $ do
    [x,y,z] <- forAll $ hlist [sets, sets, sets]
    union x (union y z) === union (union x y) z

prop_unionCommutative : Property
prop_unionCommutative =
  property $ do
    [x,y] <- forAll $ hlist [sets, sets]
    union x y === union y x

prop_unionEmpty : Property
prop_unionEmpty =
  property $ do
    r <- forAll sets
    union r empty === r

prop_unionFull : Property
prop_unionFull =
  property $ do
    r <- forAll sets
    union r fullSet === fullSet

prop_intersectionCommutative : Property
prop_intersectionCommutative =
  property $ do
    [x,y] <- forAll $ hlist [sets, sets]
    intersection x y === intersection y x

prop_intersectionAssociative : Property
prop_intersectionAssociative =
  property $ do
    [x,y,z] <- forAll $ hlist [sets, sets, sets]
    intersection x (intersection y z) === intersection (intersection y x) z

prop_intersectionEmpty : Property
prop_intersectionEmpty =
  property $ do
    x <- forAll sets
    intersection x empty === empty

prop_intersectionFull : Property
prop_intersectionFull =
  property $ do
    x <- forAll sets
    intersection x fullSet === x

--------------------------------------------------------------------------------
-- props
--------------------------------------------------------------------------------

export
props : Group
props =
  MkGroup "Text.ILex.Char.Range"
    [ ("prop_unionAssociative", prop_unionAssociative)
    , ("prop_unionCommutative", prop_unionCommutative)
    , ("prop_unionEmpty", prop_unionEmpty)
    , ("prop_unionFull", prop_unionFull)
    , ("prop_intersectionAssociative", prop_intersectionAssociative)
    , ("prop_intersectionCommutative", prop_intersectionCommutative)
    , ("prop_intersectionEmpty", prop_intersectionEmpty)
    , ("prop_intersectionFull", prop_intersectionFull)
    ]

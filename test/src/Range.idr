module Range

import Data.List.Quantifiers
import Data.Vect
import Hedgehog
import Text.ILex.Char.Range

%default total

ranges : Gen Range
ranges = frequency [(1, pure Empty), (20, rng)]
  where
    rng : Gen Range
    rng =
      (\[x,y] => range (min x y) (max x y)) <$> hlist [anyBits32, anyBits32]

prop_emptyHas : Property
prop_emptyHas =
  property $ do
    b <- forAll anyBits32
    has Empty b === False

prop_singletonHas : Property
prop_singletonHas =
  property $ do
    b <- forAll $ anyBits32
    has (singleton b) b === True

prop_rangeHas : Property
prop_rangeHas =
  property $ do
    [x,y] <- forAll $ hlist [anyBits32, anyBits32]
    let rng := range (min x y) (max x y)
    has rng x === True
    has rng y === True

prop_unionOverlap : Property
prop_unionOverlap =
  property $ do
    [x,y] <- forAll $ hlist [ranges, ranges]
    when (overlap x y) (Left (span x y) === union x y)

prop_unionAdjacent : Property
prop_unionAdjacent =
  property $ do
    [x,y] <- forAll $ hlist [ranges, ranges]
    when (adjacent x y) (Left (span x y) === union x y)

prop_unionCommutative : Property
prop_unionCommutative =
  property $ do
    [x,y] <- forAll $ hlist [ranges, ranges]
    union x y === union y x

prop_unionEmpty : Property
prop_unionEmpty =
  property $ do
    r <- forAll ranges
    union r Empty === Left r

prop_unionFull : Property
prop_unionFull =
  property $ do
    r <- forAll ranges
    union r fullRange === Left fullRange

prop_intersectionCommutative : Property
prop_intersectionCommutative =
  property $ do
    [x,y] <- forAll $ hlist [ranges, ranges]
    intersection x y === intersection y x

prop_intersectionAssociative : Property
prop_intersectionAssociative =
  property $ do
    [x,y,z] <- forAll $ hlist [ranges, ranges, ranges]
    intersection x (intersection y z) === intersection (intersection y x) z

prop_intersectionEmpty : Property
prop_intersectionEmpty =
  property $ do
    x <- forAll ranges
    intersection x Empty === Empty

prop_intersectionFull : Property
prop_intersectionFull =
  property $ do
    x <- forAll ranges
    intersection x fullRange === x

--------------------------------------------------------------------------------
-- props
--------------------------------------------------------------------------------

export
props : Group
props =
  MkGroup "Text.ILex.Char.Range"
    [("prop_emptyHas", prop_emptyHas)
    ,("prop_singletonHas", prop_singletonHas)
    ,("prop_rangeHas", prop_rangeHas)
    ,("prop_unionOverlap", prop_unionOverlap)
    ,("prop_unionAdjacent", prop_unionAdjacent)
    ,("prop_unionCommutative", prop_unionCommutative)
    ,("prop_unionEmpty", prop_unionEmpty)
    ,("prop_unionFull", prop_unionFull)
    ,("prop_intersectionAssociative", prop_intersectionAssociative)
    ,("prop_intersectionCommutative", prop_intersectionCommutative)
    ,("prop_intersectionEmpty", prop_intersectionEmpty)
    ,("prop_intersectionFull", prop_intersectionFull)
    ]

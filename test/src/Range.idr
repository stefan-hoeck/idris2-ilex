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
    ]

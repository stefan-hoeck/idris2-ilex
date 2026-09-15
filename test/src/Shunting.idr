module Shunting

import Hedgehog
import Shunting.Parser
import Text.ILex

%default total

fromInteger : Integer -> Term
fromInteger = TNat . cast

FromString BOp where
  fromString "+" = pure PLUS
  fromString _   = pure NEG

prop_leftAssoc : Property
prop_leftAssoc =
  property1 $
    testTerm "1 + 2 + 3 + 4;" === Right [TI (TI (TI 1 "+" 2) "+" 3) "+" 4]

export
props : Group
props =
  MkGroup "Text.ILex.Shunting"
    [("prop_leftAssoc", prop_leftAssoc)
    ]

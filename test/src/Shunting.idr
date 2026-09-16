module Shunting

import Hedgehog
import Shunting.Parser
import Text.ILex

%default total

prop_leftAssoc : Property
prop_leftAssoc =
  property1 $
    testTerm "1 + 2 + 3 + 4;" === Right [((TNat 1 + TNat 2) + TNat 3) + TNat 4]

prop_mixedInfix : Property
prop_mixedInfix =
  property1 $
    testTerm "1 + 2 * 3 - 4 * 5 * 6 + -1;" ===
      Right [((TNat 1 + (TNat 2 * TNat 3)) - ((TNat 4 * TNat 5) * TNat 6)) + negate 1]

export
props : Group
props =
  MkGroup "Text.ILex.Shunting"
    [("prop_leftAssoc", prop_leftAssoc)
    ,("prop_mixedInfix", prop_mixedInfix)
    ]

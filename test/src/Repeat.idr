module Repeat

import Data.Either
import Derive.Prelude
import Hedgehog
import Derive.Pretty
import Text.ILex
import Text.ILex.Debug
import Runner

%default total
%language ElabReflection

public export
data ABC : Type where
  A  : ABC
  B  : ABC
  C  : ABC
  D  : ABC

%runElab derive "ABC" [Show,Eq]

export
Interpolation ABC where interpolate = show

export
Pretty ABC where prettyPrec _ v = line (show v)

spaces : RExp True
spaces = plus (oneof [' ', '\n', '\r', '\t'])

abc : Lexer b Void ABC
abc =
  lexer $ dfa
    [ ('A' >> repeat  4 'a', const A)
    , ('B' >> atmost  3 'b', const B)
    , ('C' >> atleast 3 'c', const C)
    , ('D' >> repeatRange 2 5 'd', const D)
    , (spaces, Ignore)
    ]

prop_AOnly : Property
prop_AOnly =
  property1 $ do
    Right [ B A $ BS 0 4 ] === lexBounds abc "Aaaaa"
    assert $ isLeft (lexBounds abc "Aaaa")
    assert $ isLeft (lexBounds abc "Aaaaaa")

prop_BOnly : Property
prop_BOnly =
  property1 $ do
    Right [ B B $ BS 0 0 ] === lexBounds abc "B"
    Right [ B B $ BS 0 1 ] === lexBounds abc "Bb"
    Right [ B B $ BS 0 2 ] === lexBounds abc "Bbb"
    Right [ B B $ BS 0 3 ] === lexBounds abc "Bbbb"
    assert $ isLeft (lexBounds abc "Bbbbb")

prop_COnly : Property
prop_COnly =
  property1 $ do
    Right [ B C $ BS 0 3 ] === lexBounds abc "Cccc"
    Right [ B C $ BS 0 4 ] === lexBounds abc "Ccccc"
    Right [ B C $ BS 0 5 ] === lexBounds abc "Cccccc"
    Right [ B C $ BS 0 6 ] === lexBounds abc "Ccccccc"
    assert $ isLeft (lexBounds abc "Ccc")
    assert $ isLeft (lexBounds abc "Cc")

prop_DOnly : Property
prop_DOnly =
  property1 $ do
    Right [ B D $ BS 0 2 ] === lexBounds abc "Ddd"
    Right [ B D $ BS 0 3 ] === lexBounds abc "Dddd"
    Right [ B D $ BS 0 4 ] === lexBounds abc "Ddddd"
    Right [ B D $ BS 0 5 ] === lexBounds abc "Dddddd"
    assert $ isLeft (lexBounds abc "Dd")
    assert $ isLeft (lexBounds abc "D")
    assert $ isLeft (lexBounds abc "Ddddddd")

export
props : Group
props =
  MkGroup "Text.ILex.RExp"
    [ ("prop_AOnly", prop_AOnly)
    , ("prop_BOnly", prop_BOnly)
    , ("prop_COnly", prop_COnly)
    , ("prop_DOnly", prop_DOnly)
    ]

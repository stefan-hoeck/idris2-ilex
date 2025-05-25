module FC

import Data.Buffer
import Data.String
import Hedgehog
import Text.ILex

%default total

alphaStrs : Gen String
alphaStrs = string (linear 0 30) alphaNum

unicodeStrs : Gen String
unicodeStrs = string (linear 0 30) printableUnicode

toBS : String -> ByteString
toBS = fromString

manyToBS : List String -> ByteString
manyToBS = toBS . fastConcat

prop_inAlpha : Property
prop_inAlpha =
  property $ do
    s   <- forAll alphaStrs
    let l := length s
    P 0 l === toPosition l (fromString s)

prop_inUnicode : Property
prop_inUnicode =
  property $ do
    s   <- forAll unicodeStrs
    let bs := toBS s
    P 0 (length s) === toPosition bs.size bs

prop_inAlphaLines : Property
prop_inAlphaLines =
  property $ do
    ss <- forAll $ list (linear 1 10) alphaStrs
    let bs := manyToBS $ intersperse "\n" ss
        l  := foldl (\_ => String.length) 0 ss -- length of last line
    P (pred $ length ss) l === toPosition bs.size bs

prop_inUnicodeLines : Property
prop_inUnicodeLines =
  property $ do
    ss <- forAll $ list (linear 1 10) unicodeStrs
    let bs := manyToBS $ intersperse "\n" ss
        l  := foldl (\_ => String.length) 0 ss -- length of last line
    P (pred $ length ss) l === toPosition bs.size bs

export
props : Group
props =
  MkGroup "Text.ILex.FC"
    [ ("prop_inAlpha", prop_inAlpha)
    , ("prop_inUnicode", prop_inUnicode)
    , ("prop_inAlphaLines", prop_inAlphaLines)
    , ("prop_inUnicodeLines", prop_inUnicodeLines)
    ]

module ByteRange

import Data.ByteString
import Data.List.Quantifiers
import Data.List
import Data.Vect
import Hedgehog
import Text.ByteRange

%default total

chr : Gen Char
chr = frequency [(1, pure '\n'), (5, unicode)]

bytes : Gen ByteString
bytes = fromString <$> string (linear 1 200) chr

chunks : List Nat -> ByteString -> List ByteString
chunks []        x = [x]
chunks (n :: ns) x =
  let Just (a,b) := splitAt n x | Nothing => [x]
   in a :: chunks ns b

quote : ByteString -> String
quote bs = "'\{bs}'"

printChunks : List ByteString -> String
printChunks = fastConcat . intersperse ", " . map quote

bytePos : BytePos -> Nat -> Gen BytePos
bytePos p n = BP <$> nat (linear p.pos $ pred n)

compRange : (s,e : BytePos) -> List ByteString -> ByteRange
compRange s e bss = enclosingBytes s e bss

compBounds : (s,e : BytePos) -> List ByteString -> Maybe Bounds
compBounds s e bss = map absolute (textBounds s e $ compRange s e bss)

problematic : List ByteString
problematic = [ pack [11,11], pack [11,11,10,10,10,10,10], pack [10,11,11]]

prop_enclosingBounds : Property
prop_enclosingBounds =
  property $ Prelude.do
    [bs,ns] <- forAll $ hlist [bytes, list (linear 0 20) (nat $ linear 1 10)]
    s       <- forAll (bytePos 0 bs.size)
    e       <- forAll (bytePos s bs.size)
    let bss := chunks ns bs
        m   := bytePositionMap bs
        exp := toBounds (BB s e)
    Just exp === compBounds s e bss

prop_bug : Property
prop_bug = property1 $ Just (BS (P 0 3) (P 5 0)) === compBounds 3 9 problematic

export
props : Group
props =
  MkGroup "Text.ByteRange"
    [ ("prop_enclosingBounds", prop_enclosingBounds)
    , ("prop_bug", prop_bug)
    ]

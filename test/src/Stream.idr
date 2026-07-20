module Stream

import Data.List.Quantifiers
import Context
import Data.Vect
import Hedgehog
import Text.ILex

%default total

bytes : Gen ByteString
bytes =
 let tok := Prelude.[| (snd <$> choice [genNum, genStr]) ++ space |]
  in (fromString . fastConcat) <$> list (linear 0 50) tok

chunks : List Nat -> ByteString -> List ByteString
chunks []        x = [x]
chunks (n :: ns) x =
  let Just (a,b) := splitAt n x | Nothing => [x]
   in a :: chunks ns b

quote : ByteString -> String
quote bs = "'\{bs}'"

printChunks : List ByteString -> String
printChunks = fastConcat . intersperse ", " . map quote

-- parsing a list of chunks should lead to exactly the same
-- result as parsing the concatenated chunks as a whole
-- this is THE proof of concept for streaming!
prop_parseChunks : Property
prop_parseChunks =
  property $ do
    [ns,bs] <- forAll $ hlist [list (linear 0 10) (nat $ linear 0 10), bytes]
    let cs := chunks ns bs
    footnote "bytes:  '\{bs}'"
    footnote "chunks: \{printChunks cs}"
    runBytes lit bs === runList lit (chunks ns bs)

export
props : Group
props =
  MkGroup "Text.ILex.Runner.runList"
    [("prop_parseChunks", prop_parseChunks)]

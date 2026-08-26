||| Conversion of the bounds of a byte sequence to an text
||| sequence plus absolute and relative bounds for pretty printing
||| errors when streaming large files.
module Text.ByteRange

import Derive.Prelude
import public Data.ByteString
import public Text.ByteBounds

%default total
%language ElabReflection

MIN_LINES : Nat
MIN_LINES = 5

||| A non-empty chunk of bytes in a sequence or stream of bytes
||| wrapped up with some counters.
public export
record Chunk where
  constructor CH
  ||| The current chunk of bytes
  bytes       : ByteString

  ||| Absolute byte position of the first byte in `bytes`
  first       : BytePos

  ||| Number of line breaks encountered before this chunk
  linesBefore : Nat

  ||| Number of line breaks in this chunk
  lines       : Nat

  {auto 0 prf : IsSucc bytes.size}

%runElab derive "Chunk" [Show]

%inline
lineCount : ByteString -> Nat
lineCount = flip foldr Z $ \b,n => case b of {0xa => S n; _   => n}

||| Absolute position of the last byte in the given `Chunk`.
export
(.last) : Chunk -> BytePos
b.last = incLen b.bytes.size b.first

||| Absolute position of the first byte of the next chunk after this one.
export
(.next) : Chunk -> BytePos
b.next = BP (b.first.pos + b.bytes.size)

||| Number of linebreaks up to and including the given chunk.
export
(.linesIncluding) : Chunk -> Nat
b.linesIncluding = b.linesBefore + b.lines

||| Given an optional previous chunk plus a non-empty byte vector,
||| computes the stats of the current chunk.
export
nextChunk : Maybe Chunk -> (bs : ByteString) -> (0 p : IsSucc bs.size) => Chunk
nextChunk Nothing  bs = CH bs 0 0 (lineCount bs)
nextChunk (Just c) bs = CH bs c.next c.linesIncluding (lineCount bs)

dropPartialLine : Chunk -> SnocList Chunk
dropPartialLine c =
 let (pre, BS (S $ S k) pst) := break (0xa ==) c.bytes | _ => [<]
     p         := BP $ c.first.pos + pre.size + 1
  in [<CH (BS (S k) $ tail pst) p (S c.linesBefore) (pred c.lines)]

||| A sequence of chunks, describing if it holds some start
||| and end position.
public export
data ByteRange : Type where
  Prefix : SnocList Chunk -> ByteRange
  Start  : SnocList Chunk -> ByteRange
  End    : SnocList Chunk -> ByteRange
  Done   : SnocList Chunk -> ByteRange
  None   : ByteRange

%runElab derive "ByteRange" [Show]

export %inline
isDone : ByteRange -> Bool
isDone (Done _) = True
isDone _        = False

containsEnd : ByteRange -> Bool
containsEnd (End _) = True
containsEnd r       = isDone r

export
chunks : ByteRange -> SnocList Chunk
chunks (Prefix sx) = sx
chunks (Start sx)  = sx
chunks (End sx)    = sx
chunks (Done sx)   = sx
chunks None        = [<]

lastChunk : SnocList Chunk -> Maybe Chunk
lastChunk [<]    = Nothing
lastChunk (_:<c) = Just c

pre : List Chunk -> SnocList Chunk -> Nat -> ByteRange
pre cs [<] _     = Prefix ([<] <>< cs)
pre cs (sc:<c) n =
  case n `minus` c.lines of
    0 => Start (dropPartialLine c <>< cs)
    n => pre (c::cs) sc n

||| Given a start and end position, appends a chunk of bytes to
||| range of bytes, making sure that the range will contain
||| enough lines before the start byte and enough lines after the
||| end byte.
export
appendChunk : (s,e : BytePos) -> ByteRange -> ByteString -> ByteRange
appendChunk _ _ r@(Done _) _               = r
appendChunk _ _ r          (BS 0 _)        = r
appendChunk s e r          bs@(BS (S _) _) =
 let cs  := chunks r
     c   := nextChunk (lastChunk cs) bs
     cs2 := cs:<c
  in case c.last >= e of
       True  => if containsEnd r && c.lines > 0 then Done cs2 else End cs2
       False => case c.first >= s of
         True  => Start cs2
         False => pre [] cs2 MIN_LINES

||| Given a sequence (or stream) of byte vectors, we want to find
||| a minimal chunk fully enclosing a given byte range, so that we
||| can pretty print that byte range.
|||
||| The chunk should fulfill the following prerequisites:
|||  * fully contain all bytes given in the byte range
|||  * contain the last five line breaks before the first
|||    byte in the byte range, or - if there are not as many line breaks before
|||    the first byte - contain the first byte of the whole byte stream
|||    so that we can print the whole line where - for instance -
|||    an error occurred
|||  * contain at least the next line-break *after* the last position (if any)
export %inline
enclosingBytes : Foldable f => (s,e : BytePos) -> f ByteString -> ByteRange
enclosingBytes s e = foldl (appendChunk s e) None

||| Absolute and relative text bounds in a stream of byte vectors
public export
record TextBounds where
  constructor TB
  ||| An excerpt of the byte stream large enough to fully contain
  ||| a given byte sequence
  content  : String

  ||| Absolute bounds of the start and end position of the given
  ||| byte sequence.
  absolute : Bounds

  ||| Relative bounds of the start and end position of the given
  ||| byte sequence.
  relative : Bounds

%runElab derive "TextBounds" [Show,Eq]

bounds : (line : Nat) -> ByteBounds -> ByteString -> TextBounds
bounds line bb bs =
 let ini := P line 0
     m   := bytePositionMapFrom ini bs
     abs := toBounds bb
  in TB (toString bs) abs (relativeTo abs ini)

||| Given a byte range that is supposed to contain the
||| byte sequence corresponding to the given byte bounds,
||| returns the proper text bounds - or `Nothing` if
||| something went wrong.
export
textBounds : (start, end : BytePos) -> ByteRange -> Maybe TextBounds
textBounds s e r =
  case containsEnd r of
    False => Nothing
    True  =>
     let c::cs := chunks r <>> [] | _ => Nothing
         bs    := fastConcat (map bytes $ c::cs)
         o     := c.first
      in Just $ bounds c.linesBefore (BB (offsetTo o s) (offsetTo o e)) bs

export %inline
toFCErr : ByteError e -> TextBounds -> FCErr e
toFCErr (BE o _ _ x) (TB c a r) = PE o a r (Just c) x

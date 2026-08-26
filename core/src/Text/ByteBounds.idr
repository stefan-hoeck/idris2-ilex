module Text.ByteBounds

import Data.Array.Core
import Data.Bits
import Data.ByteString
import Derive.Prelude
import public Text.Bounds
import public Text.FC
import public Text.ParseError

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Position
--------------------------------------------------------------------------------

||| Position in a byte string or stream.
public export
record BytePos where
  constructor BP
  pos  : Nat

%runElab derive "BytePos" [Show,Eq,Ord,FromInteger]

public export %inline
Interpolation BytePos where
  interpolate = show . pos

||| Increases the position by the given length
||| of a byte sequence.
export
incLen : Nat -> BytePos -> BytePos
incLen (S n) (BP p) = BP (n+p)
incLen _     p      = p

||| Computes the end position of a token by reducing
||| the start position of the next token by one
||| (unless this is a zero-byte token corresponding to the
||| end of input).
export
endPos : (from, till : Nat) -> BytePos
endPos from till =
  case prim__lt_Integer (cast from) (cast till) of
    0 => BP till
    _ => BP (pred till)

--------------------------------------------------------------------------------
--          ByteBounds
--------------------------------------------------------------------------------

||| A pair of `BytePos`s, describing a range in a byte stream, or `NoBB` for
||| use - for instance - with programmatically created tokens.
public export
data ByteBounds : Type where
  BB   : (start, end : BytePos) -> ByteBounds
  NoBB : ByteBounds

%runElab derive "ByteBounds" [Show,Eq]

export
Interpolation ByteBounds where
  interpolate (BB s e) = if s == e then "\{s}" else "\{s}--\{e}"
  interpolate NoBB     = ""

public export
Semigroup ByteBounds where
  NoBB     <+> y        = y
  x        <+> NoBB     = x
  BB s1 e1 <+> BB s2 e2 = BB (min s1 s2) (max e1 e2)

public export
Monoid ByteBounds where
  neutral = NoBB

public export
interface MapBounds (0 a : Type) where
  mapBounds : (ByteBounds -> ByteBounds) -> a -> a

export %inline
clearBounds : MapBounds a => a -> a
clearBounds = mapBounds (const NoBB)

export %inline
MapBounds ByteBounds where mapBounds = id

export
MapBounds a => MapBounds (Maybe a) where
  mapBounds = map . mapBounds

export
MapBounds a => MapBounds (List a) where
  mapBounds = map . mapBounds

export
MapBounds a => MapBounds (SnocList a) where
  mapBounds = map . mapBounds

export
MapBounds a => MapBounds b => MapBounds (a,b) where
  mapBounds f (x,y) = (mapBounds f x, mapBounds f y)

export
MapBounds a => MapBounds b => MapBounds (Either a b) where
  mapBounds f (Left x)  = Left $ mapBounds f x
  mapBounds f (Right x) = Right $ mapBounds f x

export %inline
fromPos : Cast t ByteBounds => BytePos -> t -> ByteBounds
fromPos p x = BB p p <+> cast x

export %inline
tillPos : Cast t ByteBounds => t -> BytePos -> ByteBounds
tillPos x p = cast x <+> BB p p

export %inline
Cast BytePos ByteBounds where cast b = BB b b

--------------------------------------------------------------------------------
--          ByteBounded
--------------------------------------------------------------------------------

||| Pairs a value with the bounds in the byte stream from where it was parsed.
public export
record ByteBounded ty where
  constructor B
  val    : ty
  bounds : ByteBounds

%runElab derive "ByteBounded" [Show,Eq]

export
fromBytePos : ByteBounded a -> BytePos -> ByteBounded a
fromBytePos (B v $ BB (BP s) (BP e)) (BP p) = B v $ BB (BP $ s+p) (BP $ e+p)
fromBytePos (B v NoBB)               p      = B v $ BB p p

-- implements of `(<*>)`
app : ByteBounded (a -> b) -> ByteBounded a -> ByteBounded b
app (B vf b1) (B va b2) = B (vf va) (b1 <+> b2)

-- implements `(>>=)`
bind : ByteBounded a -> (a -> ByteBounded b) -> ByteBounded b
bind (B va b1) f =
  let B vb b2 = f va
   in B vb (b1 <+> b2)

export
Functor ByteBounded where
  map f (B val bs) = B (f val) bs

export %inline
Applicative ByteBounded where
  pure v = B v neutral
  (<*>) = app

export %inline
Monad ByteBounded where
  (>>=) = bind

export
Foldable ByteBounded where
  foldr c n b = c b.val n
  foldl c n b = c n b.val
  foldMap f b = f b.val
  null _ = False
  toList b = [b.val]

export
Traversable ByteBounded where
  traverse f (B v bs) = (`B` bs) <$> f v

export %inline
MapBounds (ByteBounded a) where mapBounds f = {bounds $= f}

--------------------------------------------------------------------------------
--          Conversion to Bounds
--------------------------------------------------------------------------------

public export
record PositionMap where
  [noHints]
  constructor PM
  size : Nat
  arr  : IArray size Position

%runElab derive "PositionMap" [Show]

export
Eq PositionMap where
  PM _ x == PM _ y = heq x y

export %inline
bytePositionMapFrom : Position -> ByteString -> PositionMap
bytePositionMapFrom p (BS n bv) = PM (S n) $ positionMapFrom p bv

export %inline
stringPositionMapFrom : Position -> String -> PositionMap
stringPositionMapFrom p = bytePositionMapFrom p . fromString

export %inline
bytePositionMap : ByteString -> PositionMap
bytePositionMap (BS n bv) = PM (S n) $ positionMap bv

export %inline
stringPositionMap : String -> PositionMap
stringPositionMap = bytePositionMap . fromString

parameters {auto pm : PositionMap}
  export %inline
  position : BytePos -> Maybe Position
  position (BP n) =
    case tryLT n of
      Just0 x  => Just $ atNat pm.arr n @{x}
      Nothing0 => Nothing

  export
  toBounds : ByteBounds -> Bounds
  toBounds NoBB               = NoBounds
  toBounds (BB x y) =
   let Just px := position x | _ => NoBounds
       Just py := position y | _ => NoBounds
    in BS px py

  export
  toBounded : ByteBounded a -> Bounded a
  toBounded (B v bs) = B v $ toBounds bs

public export
0 BBErr : Type -> Type
BBErr e = ByteBounded (InnerError e)

||| Converts an error with byte bounds to a `ParseError` by pairing it with
||| an origin and the parsed string.
export
toParseError : Origin -> String -> BBErr e -> ParseError e
toParseError o s err =
 let mp := stringPositionMap s
  in toParseError o s (toBounded err)

--------------------------------------------------------------------------------
--          Conversion to Bounds
--------------------------------------------------------------------------------

public export
record ByteContext where
  constructor BC
  origin  : Origin
  bounds  : ByteBounds

%runElab derive "ByteContext" [Show,Eq]

export
Interpolation ByteContext where
  interpolate (BC o NoBB) = interpolate o
  interpolate (BC o bs)   = "\{o}: \{bs}"

export %inline
MapBounds ByteContext where mapBounds f = {bounds $= f}

public export
record ByteError e where
  constructor BE
  origin  : Origin
  bounds  : ByteBounds
  content : Maybe ByteString
  error   : e

%runElab derive "ByteError" [Show,Eq]

export %inline
MapBounds (ByteError e) where mapBounds f = {bounds $= f}

public export
0 ByteErr : Type -> Type
ByteErr = ByteError . InnerError

export
byteError : Origin -> ByteBounded e -> ByteError e
byteError o (B err bs) = BE o bs Nothing err

boundsPart : ByteBounds -> String
boundsPart NoBB     = ""
boundsPart (BB s e) =
  case s == e of
    True  => ", byte \{s}"
    False => ", bytes \{s}--\{e}"

export
prettyByteErr : Interpolation e => ByteError e -> String
prettyByteErr (BE o bb m err) =
  case m of
    Nothing => "Error at \{o}\{boundsPart bb}: \{err}"
    Just bs =>
     let mp := bytePositionMap bs
      in interpolate $ toParseError o (toString bs) (toBounded $ B err bb)

export %inline
Interpolation e => Interpolation (ByteError e) where
  interpolate = prettyByteErr

--------------------------------------------------------------------------------
--          Conversion to (relative) Text Bounds
--------------------------------------------------------------------------------

MIN_LINES : Nat
MIN_LINES = 5

public export
record Chunk where
  constructor CH
  bytes       : ByteString
  first       : BytePos
  linesBefore : Nat
  lines       : Nat

lineCount : ByteString -> Nat
lineCount = foldr (\b,n => case b of {0xa => S n; _ => n}) 0

export
(.last) : Chunk -> BytePos
b.last = incLen b.bytes.size b.first

export
(.next) : Chunk -> BytePos
b.next = BP (b.first.pos + b.bytes.size)

export
(.linesAfter) : Chunk -> Nat
b.linesAfter = b.linesBefore + b.lines

public export
data ByteRange : Type where
  Prefix : SnocList Chunk -> ByteRange
  Start  : SnocList Chunk -> ByteRange
  End    : SnocList Chunk -> ByteRange
  Done   : SnocList Chunk -> ByteRange
  None   : ByteRange

containsEnd : ByteRange -> Bool
containsEnd (End _)  = True
containsEnd (Done _) = True
containsEnd _        = False

export
chunks : ByteRange -> SnocList Chunk
chunks (Prefix sx) = sx
chunks (Start sx)  = sx
chunks (End sx)    = sx
chunks (Done sx)   = sx
chunks None        = [<]

lastChunk : SnocList Chunk -> Chunk
lastChunk [<]    = CH empty 0 0 0
lastChunk (_:<c) = c

export
nextChunk : Chunk -> ByteString -> Chunk

pre : List Chunk -> SnocList Chunk -> Nat -> ByteRange

export
appendChunk : (s,e : BytePos) -> ByteRange -> ByteString -> ByteRange
appendChunk s e br bs =
 let cs  := chunks br
     lc  := lastChunk cs
     c   := nextChunk lc bs
     cs2 := cs:<c
  in case c.last >= e of
       True  => if containsEnd br && c.lines > 0 then Done cs2 else End cs2
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
|||    the error occurred - contain the first byte of the whole byte stream
|||    so that we can print the whole line where
|||    - for instance - an error occurred
|||  * contain at least the next line-break *after* the last position
export
enclosingBytes : List ByteString -> (s,e : BytePos) -> ByteRange

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

export
inc : Nat -> BytePos -> BytePos
inc n (BP p) = BP (n+p)

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
  interpolate (BB s e) = "\{s}--\{e}"
  interpolate NoBB     = ""

public export
Semigroup ByteBounds where
  NoBB     <+> y        = y
  x        <+> NoBB     = x
  BB s1 e1 <+> BB s2 e2 = BB (min s1 s2) (max e1 e2)

public export
Monoid ByteBounds where
  neutral = NoBB

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
bytePositionMapFrom p (BS n bv) = PM n $ positionMapFrom p bv

export %inline
stringPositionMapFrom : Position -> String -> PositionMap
stringPositionMapFrom p = bytePositionMapFrom p . fromString


export %inline
bytePositionMap : ByteString -> PositionMap
bytePositionMap (BS n bv) = PM n $ positionMap bv

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
  toBounds (BB (BP x) (BP y)) =
   let Just0 px := tryLT {n = pm.size} x | _ => NoBounds
       Just0 py := tryLT {n = pm.size} y | _ => NoBounds
    in BS (atNat pm.arr x) (atNat pm.arr y)

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

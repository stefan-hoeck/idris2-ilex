module Text.ByteBounds

import Data.Bits
import Data.ByteString
import Derive.Prelude

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

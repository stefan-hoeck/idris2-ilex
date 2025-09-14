module Text.ILex.Bounds

import Data.Bits
import Data.ByteString
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Bounds
--------------------------------------------------------------------------------

||| Position (line and column; both zero-based) in a string.
public export
record Position where
  constructor P
  line   : Nat
  column : Nat

%runElab derive "Position" [Show,Eq,Ord]

public export
Interpolation Position where
  interpolate (P l c) = show (l+1) ++ ":" ++ show (c+1)

||| The beginning of a string. This is an alias for `P 0 0`.
public export
begin : Position
begin = P 0 0

||| Increase the current column by one.
public export %inline
incCol : Nat -> Position -> Position
incCol n (P l c) = P l (n+c)

||| Increase the current line by one, resetting the
||| column to 0.
public export %inline
incLine : Position -> Position
incLine p = P (S p.line) 0

export
relativeTo : Position -> Position -> Position
relativeTo (P l c) (P ls cs) =
  if l <= ls then P 0 (c `minus` cs) else P (l `minus` ls) c

||| Advances the given text position by the characters encountered
||| in the given string.
|||
||| A line feed character ('\n'; codepoint `0x0A`) will increase
||| the current line by one and reset the column to zero. Every
||| other character will increase the column by one.
export
incString : String -> Position -> Position
incString s (P l c) = go l c (unpack s)
  where
    go : Nat -> Nat -> List Char -> Position
    go l c []        = P l c
    go l c ('\n' :: xs) = go (S l) 0 xs
    go l c (x    :: xs) = go l (S c) xs

||| Advances the given text position by the bytes encountered
||| in the given string.
|||
||| A line feed byte (`0x0A`) will increase
||| the current line by one and reset the column to zero. Every
||| other start character of a unicode code point will advance
||| the column by one.
export
incBytes : ByteString -> Position -> Position
incBytes (BS n bv) (P l c) = go l c n
  where
    go : Nat -> Nat -> (k : Nat) -> (x : Ix k n) => Position
    go l c 0     = P l c
    go l c (S k) =
      case bv `ix` k of
        0x0a => go (S l) 0 k
        b    => case b < 128 || b .&. 0b1100_0000 == 0b1100_000 of
          True => go l (S c) k
          _    => go l c k

||| Upper and lower bounds of a region in a string.
|||
||| In case of non-empty bounds, the `end` is one column
||| past the last character of a token, to facilitate the
||| arithmetics when creating the bounds as well as when
||| printing emphasis marks in error messages. This is as
||| it is done in the Idris compiler itself.
public export
data Bounds : Type where
  Empty : Bounds
  BS    : (start,end : Position) -> Bounds

%runElab derive "Bounds" [Show,Eq,Ord]

export
atPos : Position -> Bounds
atPos p = BS p (incCol 1 p)

namespace Bounds
  export
  relativeTo : Bounds -> Position -> Bounds
  relativeTo Empty _    = Empty
  relativeTo (BS s e) p = BS (s `relativeTo` p) (e `relativeTo` p)

export
Semigroup Bounds where
  Empty  <+> y      = y
  x      <+> Empty  = x
  BS u v <+> BS x y = BS (min u x) (max v y)


export %inline
Monoid Bounds where neutral = Empty

export
Interpolation Bounds where
  interpolate Empty    = "<empty>"
  interpolate (BS s e) = if s == e then "\{s}" else "\{s}--\{e}"

--------------------------------------------------------------------------------
--          Bounded
--------------------------------------------------------------------------------

||| Pairs a value with the textual bounds from where it was parsed.
public export
record Bounded ty where
  constructor B
  val    : ty
  bounds : Bounds

%runElab derive "Bounded" [Show,Eq]

export
Interpolation a => Interpolation (Bounded a) where
  interpolate (B v Empty) = interpolate v
  interpolate (B v bs)    = "\{v}: \{bs}"

-- Implementation of `(<*>)`
appb : Bounded (a -> b) -> Bounded a -> Bounded b
appb (B vf b1) (B va b2) = B (vf va) (b1 <+> b2)

-- Implementation of `(>>=)`
bind : Bounded a -> (a -> Bounded b) -> Bounded b
bind (B va b1) f =
  let B vb b2 = f va
   in B vb (b1 <+> b2)

export %inline
Functor Bounded where
  map f (B val bs) = B (f val) bs

export %inline
Applicative Bounded where
  pure v = B v neutral
  (<*>) = appb

export %inline
Monad Bounded where
  (>>=) = bind

export
Foldable Bounded where
  foldr c n b = c b.val n
  foldl c n b = c n b.val
  foldMap f b = f b.val
  null _ = False
  toList b = [b.val]

export
Traversable Bounded where
  traverse f (B v bs) = (`B` bs) <$> f v

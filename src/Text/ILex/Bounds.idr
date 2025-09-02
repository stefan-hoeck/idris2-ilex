module Text.ILex.Bounds

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
incCol : Position -> Position
incCol = {column $= S}

||| Increase the current line by one, resetting the
||| column to 0.
public export %inline
incLine : Position -> Position
incLine p = P (S p.line) 0

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
atPos p = BS p (incCol p)

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

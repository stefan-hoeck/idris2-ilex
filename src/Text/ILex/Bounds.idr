module Text.ILex.Bounds

import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Bounds
--------------------------------------------------------------------------------

public export
record Position where
  constructor P
  line : Nat
  col  : Nat

%runElab derive "Position" [Show,Eq,Ord]

public export
Interpolation Position where
  interpolate (P l c) = show (l+1) ++ ":" ++ show (c+1)

||| Upper and lower bounds of a region in a byte array.
public export
data Bounds : Type where
  Empty : Bounds
  BS    : (x,y : Position) -> Bounds

%runElab derive "Bounds" [Show,Eq,Ord]

app : Bounds -> Bounds -> Bounds
app Empty     y       = y
app x         Empty   = x
app (BS u v) (BS x y) = BS (min u x) (max v y)

export
atPos : Position -> Bounds
atPos n = BS n n

export %inline
incLine : Bits8 -> Nat -> Nat
incLine 10 l = (S l)
incLine _  l = l

export %inline
incCol : Bits8 -> Nat -> Nat
incCol 10 _ = 0
incCol b  c =
  case prim__and_Bits8 128 b of
    0 => S c
    _ => case prim__and_Bits8 0b1100_0000 b of
      0b1100_0000 => S c
      _           => c

export %inline
Semigroup Bounds where (<+>) = app

export %inline
Monoid Bounds where neutral = Empty

--------------------------------------------------------------------------------
--          Bounded
--------------------------------------------------------------------------------

||| Pairs a value with the textual bounds from where it was parsed.
public export
record Bounded ty where
  constructor B
  val    : ty
  bounds : Bounds

%runElab derive "Bounded" [Show,Eq,Ord]

-- Implementation of `(<*>)`
appb : Bounded (a -> b) -> Bounded a -> Bounded b
appb (B vf b1) (B va b2) = B (vf va) (b1 <+> b2)

-- Implementation of `(>>=)`
bind : Bounded a -> (a -> Bounded b) -> Bounded b
bind (B va b1) f =
  let B vb b2 = f va
   in B vb (b1 <+> b2)

export
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

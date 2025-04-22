module Text.ILex.Char.Range

import Derive.Prelude

%default total
%language ElabReflection

public export
interface Ord a => Bounded a where
  minBound : a
  maxBound : a

export %inline
Bounded Bits8 where
  minBound = 0
  maxBound = 0xff

export %inline
Bounded Bits16 where
  minBound = 0
  maxBound = 0xffff

export %inline
Bounded Bits32 where
  minBound = 0
  maxBound = 0xffff_ffff

export %inline
Bounded Bits64 where
  minBound = 0
  maxBound = 0xffff_ffff_ffff_ffff

||| A range of unicode code points.
|||
||| Actually, it's a range of 32-bit numbers, but we use it for describing
||| ranges of codepoints in this library.
export
data RangeOf : (t : Type) -> Type where
  Empty : RangeOf t
  Rng   : (low,up : t) -> RangeOf t

%runElab derive "RangeOf" [Show,Eq,Ord]

public export
0 Range8 : Type
Range8 = RangeOf Bits8

public export
0 Range32 : Type
Range32 = RangeOf Bits32

||| The empty range of codepoints.
export %inline
empty : RangeOf t
empty = Empty

||| A range containing a single value
export %inline
singleton : t -> RangeOf t
singleton v = Rng v v

export %inline
isEmpty : RangeOf t -> Bool
isEmpty Empty = True
isEmpty _     = False

||| Generates a new range from `x` to `y` if `x` is strictly
||| smaller than `y`. Otherwise, the empty range is returned.
export %inline
range : Ord t => (x,y : t) -> RangeOf t
range x y =
  case x <= y of
    True  => Rng x y
    False => Empty

||| True if the value is within the range.
export
has : Ord t => RangeOf t -> t -> Bool
has Empty     _ = False
has (Rng x y) v = x <= v && v <= y

||| True if the two ranges overlap
export
overlap : Ord t => RangeOf t -> RangeOf t -> Bool
overlap r1@(Rng l1 u1) r2@(Rng l2 u2) = has r1 l2 || has r2 l1
overlap _              _              = False

||| Spans the range from the lowest to the largest bound of the two ranges.
export
span : Ord t => RangeOf t -> RangeOf t -> RangeOf t
span r1@(Rng l1 u1) r2@(Rng l2 u2) = Rng (min l1 l2) (max u1 u2)
span Empty          r              = r
span l              Empty          = l

||| Intersection of two ranges, if any.
export
intersection : Ord t => RangeOf t -> RangeOf t -> RangeOf t
intersection (Rng l1 u1) (Rng l2 u2) =
  if l1 <= l2 then range l2 (min u1 u2) else range l1 (min u2 u1)
intersection _           _           = Empty

parameters {0 t : Type}
           {auto ord : Ord t}
           {auto ng  : Neg t}


  fromTill : (x,y : t) -> RangeOf t
  fromTill x y =
    case x < y of
      True  => range x (y-1)
      False => Empty

  afterTo : (x,y : t) -> RangeOf t
  afterTo x y =
    case x < y of
      True  => range (x+1) y
      False => Empty

  ||| True if the two ranges are adjacent, that is, the upper bound
  ||| of one range is one less than the lower bound of the other.
  export
  adjacent : RangeOf t -> RangeOf t -> Bool
  adjacent (Rng l1 u1) (Rng l2 u2) =
    (u1 < l2 && (u1+1) == l2) || (u2 < l1 && (u2+1) == l1)
  adjacent _           _           = False

  ||| Union of the ranges.
  |||
  ||| If there are two results then they are guaranteed to be non-empty,
  ||| have a non-empty gap in between, and are in ascending order
  export
  union : RangeOf t -> RangeOf t -> Either (RangeOf t) (RangeOf t,RangeOf t)
  union r1@(Rng l1 u1) r2@(Rng l2 u2) =
    if overlap r1 r2 || adjacent r1 r2
       then Left (span r1 r2)
       else Right (min r1 r2, max r1 r2)
  union Empty       r           = Left r
  union l           Empty       = Left l

  ||| Returns the result of subtracting the second range from the first.
  |||
  ||| If there are two results then they are guaranteed to be non-empty,
  ||| have a non-empty gap in between, and are in ascending order
  export
  difference : RangeOf t -> RangeOf t -> Either (RangeOf t) (RangeOf t,RangeOf t)
  difference r1@(Rng l1 u1) r2@(Rng l2 u2) =
    case overlap r1 r2 of
      True  =>
        let x@(Rng _ _) := fromTill l1 l2 | Empty => Left (afterTo u2 u1)
            y@(Rng _ _) := afterTo u2 u1 | Empty => Left x
         in Right (min x y, max x y)
      False => Left r1
  difference Empty       r           = Left Empty
  difference l           Empty       = Left l

||| The range of all unicode code points.
export
codepoint : Range32
codepoint = Rng 0 0x10ffff

||| The range of surrogate pairs.
export
surrogate : Range32
surrogate = Rng 0xd800 0xdfff

||| A range corresponding to a pair of characters.
export %inline
charRange : (x,y : Char) -> Range32
charRange x y = range (cast x) (cast y)

||| The full range.  All 32 bit values are within it.
export %inline
fullRange : Bounded t => RangeOf t
fullRange = Rng minBound maxBound

||| A range is full if it contains every possible value.
export %inline
isFull : Bounded t => RangeOf t -> Bool
isFull = (== fullRange)

export
lowerBound : Bounded t => RangeOf t -> t
lowerBound (Rng l _) = l
lowerBound Empty     = maxBound

export
upperBound : Bounded t => RangeOf t -> t
upperBound (Rng _ u) = u
upperBound Empty     = minBound

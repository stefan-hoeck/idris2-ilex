module Text.ILex.Range

import Data.Refined.Bits32
import Derive.Prelude

%default total
%language ElabReflection

||| A range of unicode code points.
public export
data Range : Type where
  Empty : Range
  Rng   : (low,up : Bits32) -> (0 p : low <= up) => Range

%runElab derive "Range" [Show,Eq,Ord]

||| The empty range of codepoints.
export %inline
empty : Range
empty = Empty

||| Generates a new range from `x` to `y` if `x` is strictly
||| smaller than `y`. Otherwise, the empty range is returned.
export %inline
range : (x,y : Bits32) -> Range
range x y =
  case lte x y of
    Just0 p  => Rng x y
    Nothing0 => Empty

||| The range of all unicode code points.
export
codepoint : Range
codepoint = Rng 0 0x10ffff

||| The range of surrogate pairs.
export
surrogate : Range
surrogate = Rng 0xd800 0xdfff

||| A range corresponding to a pair of characters.
export %inline
charRange : (x,y : Char) -> Range
charRange x y = range (cast x) (cast y)

fromTill : (x,y : Bits32) -> Range
fromTill x y = if x < y then range x (y-1) else Empty

afterTo : (x,y : Bits32) -> Range
afterTo x y = if x < y then range (x+1) y else Empty

||| True if the value is within the range.
export
has : Range -> Bits32 -> Bool
has Empty     _ = False
has (Rng x y) v = x <= v && y >= v

||| True if the two ranges overlap
export
overlap : Range -> Range -> Bool
overlap r1@(Rng l1 u1) r2@(Rng l2 u2) = has r1 l2 || has r2 l1
overlap _              _              = False

prev : Bits32 -> Bits32
prev 0 = 0
prev x = x-1

||| True if the two ranges are adjacent, that is, the upper bound
||| of one range is one less than the lower bound of the other.
export
adjacent : Range -> Range -> Bool
adjacent (Rng l1 u1) (Rng l2 u2) =
  (u1 < l2 && (u1+1) == l2) || (u2 < l1 && (u2+1) == l1)
adjacent _           _           = False

||| The full range.  All 32 bit values are within it.
export %inline
fullRange : Range
fullRange = Rng 0 0xffff_ffff

||| A range containing a single value
export %inline
singleton : Bits32 -> Range
singleton v = Rng v v

export %inline
isEmpty : Range -> Bool
isEmpty = (== Empty)

||| A range is full if it contains every possible value.
export %inline
isFull : Range -> Bool
isFull = (== fullRange)

export
lowerBound : Range -> Bits32
lowerBound (Rng l _) = l
lowerBound Empty     = 0xffff_ffff

||| Spans the range from the lowest to the largest bound of the two ranges.
export
span : Range -> Range -> Range
span r1@(Rng l1 u1) r2@(Rng l2 u2) = Rng (min l1 l2) (max u1 u2)
span Empty          r              = r
span l              Empty          = l

||| Intersection of two ranges, if any.
export
intersection : Range -> Range -> Range
intersection (Rng l1 u1) (Rng l2 u2) =
  if l1 <= l2 then range l2 (min u1 u2) else range l1 (min u2 u1)
intersection _           _           = Empty

||| Union of the ranges.
|||
||| If there are two results then they are guaranteed to be non-empty,
||| have a non-empty gap in between, and are in ascending order
export
union : Range -> Range -> Either Range (Range,Range)
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
difference : Range -> Range -> Either Range (Range,Range)
difference r1@(Rng l1 u1) r2@(Rng l2 u2) =
  case overlap r1 r2 of
    True  =>
      let x@(Rng _ _) := fromTill l1 l2 | Empty => Left (afterTo u2 u1)
          y@(Rng _ _) := afterTo u2 u1 | Empty => Left x
       in Right (min x y, max x y)
    False => Left r1
difference Empty       r           = Left Empty
difference l           Empty       = Left l

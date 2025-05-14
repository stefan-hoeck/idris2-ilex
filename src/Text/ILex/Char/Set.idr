module Text.ILex.Char.Set

import Data.Vect
import Derive.Prelude
import public Text.ILex.Char.Range

%language ElabReflection
%default total

--------------------------------------------------------------------------------
-- Sets
--------------------------------------------------------------------------------

||| A set of unicode points (actually, a set of 32-bit characters)
||| represented internally as an ordered list of disjoint character
||| ranges.
export
record SetOf t where
  constructor S
  ||| A list of ordered, non-overlapping, non-adjacent, and non-empty ranges
  ranges_ : List (RangeOf t)

%runElab derive "SetOf" [Show,Eq,Ord]

public export
0 Set8 : Type
Set8 = SetOf Bits8

public export
0 Set32 : Type
Set32 = SetOf Bits32

||| Returns the inner list of ranges of a character set.
|||
||| The returned list is sorted and the ranges it contains are disjoint
||| and non-adjacent.
export %inline
ranges : SetOf t -> List (RangeOf t)
ranges = ranges_

||| The empty set of codepoints.
export
empty : SetOf t
empty = S []

||| The set holding only the given codepoint.
export
singleton : t -> SetOf t
singleton x = S [singleton x]

||| The set holding all characters in the given range.
export
range : RangeOf t -> SetOf t
range r = if isEmpty r then empty else S [r]

||| `True` if the character set is empty.
export %inline
isEmpty : SetOf t -> Bool
isEmpty (S []) = True
isEmpty _      = False

||| True if the value is within the set.
export %inline
has : Ord t => SetOf t -> t -> Bool
has (S rs) v = any (`has` v) rs

parameters {0 t : Type}
           {auto ord : WithBounds t}
           {auto ng  : Neg t}

  -- precondition: the list is already sorted
  normalise : SnocList (RangeOf t) -> Vect n (RangeOf t) -> List (RangeOf t)
  normalise sc []       = sc <>> []
  normalise sc [r]      = if isEmpty r then [] else sc <>> [r]
  normalise sc (r1 :: r2 :: t) =
    case union r1 r2 of
      Left r      => if isEmpty r then normalise sc t else normalise sc (r::t)
      Right (x,y) => normalise (sc:<x) (y::t)

  ||| Creates a character set from the given list of ranges.
  |||
  ||| The ranges are first sorted and overlapping or adjacent ranges
  ||| are unified before wrapping them up.
  export
  rangeSet : List (RangeOf t) -> SetOf t
  rangeSet rs = S . normalise [<] $ fromList (sort rs)

  ||| Set union.
  export
  union : SetOf t -> SetOf t -> SetOf t
  union (S rs) (S ss) = rangeSet (rs ++ ss)

  appendNonEmpty : SnocList (RangeOf t) -> RangeOf t -> SnocList (RangeOf t)
  appendNonEmpty sr r = if isEmpty r then sr else sr :< r

  inters :
       SnocList (RangeOf t)
    -> List (RangeOf t)
    -> List (RangeOf t)
    -> List (RangeOf t)
  inters sr l@(x::xs) r@(y::ys) =
    let sr2 := appendNonEmpty sr (intersection x y)
     in case upperBound x < upperBound y of
          True  => inters sr2 xs r
          False => inters sr2 l  ys
  inters sr _         _         = sr <>> []

  ||| Set intersection.
  export %inline
  intersection : SetOf t -> SetOf t -> SetOf t
  intersection (S rs) (S ss) = S (inters [<] rs ss)

  ||| Set negation.
  export
  negation : SetOf t -> SetOf t
  negation (S rs) = S $ go [<] 0 rs
    where
      go : SnocList (RangeOf t) -> t -> List (RangeOf t) -> List (RangeOf t)
      go sx m []        = sx <>> [range m maxBound]
      go sx m (x :: xs) =
        case isEmpty x of
          True  => go sx m xs
          False =>
           let l   := lowerBound x
               u   := upperBound x
               sx2 := if l > m then sx :< range m (l-1) else sx
            in if u == maxBound then sx2 <>> [] else go sx2 (u+1) xs

  ||| Set difference.
  export
  difference : SetOf t -> SetOf t -> SetOf t
  difference x y = intersection x (negation y)

export %inline
FromChar Set32 where
  fromChar = singleton . cast

||| The set holding the codepoints (characters) in the given
||| string.
export
chars : String -> Set32
chars = rangeSet . map (singleton . cast) . unpack

||| The set holding all 32-bit values.
export %inline
fullSet : WithBounds t => SetOf t
fullSet = range fullRange

||| `True` if this set holds all 32-bit values.
export %inline
isFull : WithBounds t => SetOf t -> Bool
isFull = (== fullSet)

--------------------------------------------------------------------------------
-- Specific Char Sets
--------------------------------------------------------------------------------

||| A range of unicode code points.
export %inline
charRange : Char -> Char -> Set32
charRange x y = range $ charRange x y

||| The set of lower-case letters.
export
lower : Set32
lower = charRange 'a' 'z'

||| The set of upper-case letters.
export
upper : Set32
upper = charRange 'A' 'Z'

||| The set of letters.
export
alpha : Set32
alpha = union lower upper

||| The set of digits.
export
digit : Set32
digit = charRange '0' '9'

||| The set of positive digits.
export
posdigit : Set32
posdigit = charRange '1' '9'

||| The set of digits and letters.
export
alphaNum : Set32
alphaNum = union alpha digit

||| The set of control characters.
export
control : Set32
control = charRange '\NUL' '\US' `union` charRange '\DEL' '\159'

||| The set of printable characters.
|||
||| This is the negation of `control`.
export
printable : Set32
printable = negation control

||| The set of ASCII characters.
export
ascii : Set32
ascii = range $ range 0 127

||| The set of non-control ASCII characters.
export
printableAscii : Set32
printableAscii = intersection ascii printable

||| The newline character ('\n')
export
nl : Set32
nl = '\n'

||| The set of unicode code points (minus surrogate pairs).
export
unicode : Set32
unicode = difference (range codepoint) (range surrogate)

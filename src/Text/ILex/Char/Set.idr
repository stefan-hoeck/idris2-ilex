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
record Set where
  constructor S
  ||| A list of ordered, non-overlapping, non-adjacent, and non-empty ranges
  ranges_ : List Range

%runElab derive "Set" [Show,Eq,Ord]

||| Returns the inner list of ranges of a character set.
|||
||| The returned list is sorted and the ranges it contains are disjoint
||| and non-adjacent.
export %inline
ranges : Set -> List Range
ranges = ranges_

-- precondition: the list is already sorted
normalise : SnocList Range -> Vect n Range -> List Range
normalise sc []       = sc <>> []
normalise sc [Empty]  = sc <>> []
normalise sc [r]      = sc <>> [r]
normalise sc (r1 :: r2 :: t) =
  case union r1 r2 of
    Left Empty  => normalise sc t
    Left r      => normalise sc (r::t)
    Right (x,y) => normalise (sc:<x) (y::t)

||| Creates a character set from the given list of ranges.
|||
||| The ranges are first sorted and overlapping or adjacent ranges
||| are unified before wrapping them up.
export
rangeSet : List Range -> Set
rangeSet rs = S . normalise [<] $ fromList (sort rs)

||| The empty set of codepoints.
export
empty : Set
empty = S []

||| The set holding only the given codepoint.
export
singleton : Bits32 -> Set
singleton x = S [singleton x]

export %inline
FromChar Set where
  fromChar = singleton . cast

||| The set holding the codepoints (characters) in the given
||| string.
export
chars : String -> Set
chars = rangeSet . map (singleton . cast) . unpack

||| The set holding all characters in the given range.
export
range : Range -> Set
range Empty = empty
range r     = S [r]

||| `True` if the character set is empty.
export %inline
isEmpty : Set -> Bool
isEmpty = (== empty)

||| The set holding all 32-bit values.
export %inline
fullSet : Set
fullSet = range fullRange

||| `True` if this set holds all 32-bit values.
export %inline
isFull : Set -> Bool
isFull = (== fullSet)

||| True if the value is within the set.
export %inline
has : Set -> Bits32 -> Bool
has (S rs) v = any (`has` v) rs

||| Set union.
export
union : Set -> Set -> Set
union (S rs) (S ss) = rangeSet (rs ++ ss)

upperBound : Range -> Bits32
upperBound (Rng _ u) = u
upperBound Empty     = 0

appendNonEmpty : SnocList Range -> Range -> SnocList Range
appendNonEmpty sr Empty = sr
appendNonEmpty sr r     = sr :< r

inters : SnocList Range -> List Range -> List Range -> List Range
inters sr l@(x::xs) r@(y::ys) =
  let sr2 := appendNonEmpty sr (intersection x y)
   in case upperBound x < upperBound y of
        True  => inters sr2 xs r
        False => inters sr2 l  ys
inters sr _         _         = sr <>> []

||| Set intersection.
export %inline
intersection : Set -> Set -> Set
intersection (S rs) (S ss) = S (inters [<] rs ss)

||| Set negation.
export
negation : Set -> Set
negation (S rs) = S $ go [<] 0 rs
  where
    go : SnocList Range -> Bits32 -> List Range -> List Range
    go sx m []        = sx <>> [range m 0xffff_ffff]
    go sx m (x :: xs) =
      case x of
        Empty   => go sx m xs
        Rng l u =>
          let sx2 := if l > m then sx :< range m (l-1) else sx
           in if u == 0xffff_ffff then sx2 <>> [] else go sx2 (u+1) xs

||| Set difference.
export
difference : Set -> Set -> Set
difference x y = intersection x (negation y)

--------------------------------------------------------------------------------
-- Specific Char Sets
--------------------------------------------------------------------------------

||| A range of unicode code points.
export %inline
charRange : Char -> Char -> Set
charRange x y = range $ charRange x y

||| The set of lower-case letters.
export
lower : Set
lower = charRange 'a' 'z'

||| The set of upper-case letters.
export
upper : Set
upper = charRange 'A' 'Z'

||| The set of letters.
export
alpha : Set
alpha = union lower upper

||| The set of digits.
export
digit : Set
digit = charRange '0' '9'

||| The set of positive digits.
export
posdigit : Set
posdigit = charRange '1' '9'

||| The set of digits and letters.
export
alphaNum : Set
alphaNum = union alpha digit

||| The set of control characters.
export
control : Set
control = charRange '\NUL' '\US' `union` charRange '\DEL' '\159'

||| The set of printable characters.
|||
||| This is the negation of `control`.
export
printable : Set
printable = negation control

||| The set of ASCII characters.
export
ascii : Set
ascii = range $ range 0 127

||| The set of non-control ASCII characters.
export
printableAscii : Set
printableAscii = intersection ascii printable

||| The newline character ('\n')
export
nl : Set
nl = '\n'

||| The set of unicode code points (minus surrogate pairs).
export
unicode : Set
unicode = difference (range codepoint) (range surrogate)

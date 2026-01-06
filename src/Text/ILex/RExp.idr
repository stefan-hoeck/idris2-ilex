module Text.ILex.RExp

import Data.Bool
import Data.ByteString
import Data.DPair
import Decidable.HDecEq
import public Text.ILex.Char.Set
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Regular Expressions
--------------------------------------------------------------------------------

||| A data type for regular expressions.
|||
||| The `Bool` flag indicates, if the regular expression consumes
||| at least one character of input or not.
public export
data RExpOf : Bool -> Type -> Type where
  Eps  : RExpOf False t
  Ch   : SetOf t -> RExpOf True t
  And  : RExpOf b1 t -> RExpOf b2 t -> RExpOf (b1 || b2) t
  Or   : RExpOf b1 t -> RExpOf b2 t -> RExpOf (b1 && b2) t
  Star : RExpOf True t -> RExpOf False t

%runElab derivePattern "RExpOf" [I,P] [Show]

public export
0 RExp : Bool -> Type
RExp b = RExpOf b Bits32

public export
0 RExp8 : Bool -> Type
RExp8 b = RExpOf b Bits8

public export
data IsCh : RExpOf b t -> Type where
  ItIsCh : IsCh (Ch s)

export
adjRanges : (SetOf t -> RExpOf True s) -> RExpOf b t -> RExpOf b s
adjRanges f Eps       = Eps
adjRanges f (Ch x)    = f x
adjRanges f (And x y) = And (adjRanges f x) (adjRanges f y)
adjRanges f (Or x y)  = Or (adjRanges f x) (adjRanges f y)
adjRanges f (Star x)  = Star (adjRanges f x)

--------------------------------------------------------------------------------
-- Token Maps
--------------------------------------------------------------------------------

public export
0 TokenMap : Type -> Type
TokenMap a = List (RExp True, a)

public export
0 TokenMap8 : Type -> Type
TokenMap8 a = List (RExp8 True, a)

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

public export
orF : RExpOf (b || False) t -> RExpOf b t
orF x = replace {p = \b => RExpOf b t} (orFalseNeutral b) x

public export
orT : RExpOf (b || True) t -> RExpOf True t
orT x = replace {p = \b => RExpOf b t} (orTrueTrue b) x

public export
toOrF : RExpOf b t -> RExpOf (b || False) t
toOrF x = replace {p = \b => RExpOf b t} (sym $ orFalseNeutral b) x

--------------------------------------------------------------------------------
-- Combinators
--------------------------------------------------------------------------------

||| Accepts the given single character
public export %inline
chr : Char -> RExp True
chr = Ch . fromChar

public export %inline
fromChar : Char -> RExp True
fromChar = chr

||| Case insensitive version of `chr`.
public export
charLike : Char -> RExp True
charLike c =
  case isLower c of
    True  => Or (chr c) (chr $ toUpper c)
    False => case isUpper c of
      True  => Or (chr c) (chr $ toLower c)
      False => chr c

parameters {auto bnd : WithBounds t}
           {auto neg : Neg t}

  public export %inline
  not : (r : RExpOf b t) -> (0 p : IsCh r) => RExpOf True t
  not (Ch s) = Ch $ negation s

  public export %inline
  (&&) : (x,y : RExpOf b t) -> (0 p : IsCh x) => (0 q : IsCh y) => RExpOf True t
  (&&) (Ch s) (Ch t) = Ch (intersection s t)

  public export %inline
  (||) : (x,y : RExpOf b t) -> (0 p : IsCh x) => (0 q : IsCh y) => RExpOf  True t
  (||) (Ch s) (Ch t) = Ch (union s t)

  public export
  (<|>) : RExpOf b1 t -> RExpOf b2 t -> RExpOf (b1 && b2) t
  Ch x <|> Ch y = Ch (union x y)
  x <|> y       = Or x y

  public export
  oneof : (rs : List (RExpOf True t)) -> (0 p : NonEmpty rs) => RExpOf True t
  oneof [r]           = r
  oneof (r::t@(_::_)) = r <|> oneof t

public export %inline
(>>) : RExpOf b1 t -> RExpOf b2 t -> RExpOf (b1 || b2) t
(>>) = And

public export %inline
eps : RExpOf False t
eps = Eps

public export %inline
opt : RExpOf True t -> RExpOf False t
opt = (`Or` eps)

||| Exactly matches the given sequence of characters
public export
chars : (cs : List Char) -> (0 p : NonEmpty cs) => RExp True
chars [c]            = chr c
chars (c::cs@(_::_)) = chr c >> chars cs

||| Case-insensitive version of `chars`
public export
charsLike : (cs : List Char) -> (0 p : NonEmpty cs) => RExp True
charsLike [c]            = charLike c
charsLike (c::cs@(_::_)) = charLike c >> charsLike cs

||| Exactly matches the given string.
public export
str : (s : String) -> (0 p : NonEmpty (unpack s)) => RExp True
str s = chars (unpack s)

||| Utility for using string literals with regular expressions.
public export %inline
fromString : (s : String) -> (0 p : NonEmpty (unpack s)) => RExp True
fromString = str

||| Case-insensitive version of `str`
public export
like : (s : String) -> (0 p : NonEmpty (unpack s)) => RExp True
like s = charsLike (unpack s)

public export
pre : (s : String) -> (0 p : NonEmpty (unpack s)) => RExp b -> RExp True
pre s r = str s >> r

public export %inline
star : RExpOf True t -> RExpOf False t
star = Star

public export %inline
plus : RExpOf True t -> RExpOf True t
plus x = x >> star x

public export
sep1 : (sep : RExpOf True t) -> RExpOf True t -> RExpOf True t
sep1 sep x = x >> star (sep >> x)

public export
sep : (sep : RExpOf True t) -> RExpOf True t -> RExpOf False t
sep s x = opt (sep1 s x)

--------------------------------------------------------------------------------
-- Repetitions
--------------------------------------------------------------------------------

public export
rep : Nat -> Bool
rep (S _) = True
rep _     = False

||| Repeats the given expression exactly `n` times
export
repeat : (n : Nat) -> RExpOf True t -> RExpOf (rep n) t
repeat 0     x = Eps
repeat (S k) x = x >> repeat k x

||| Repeats the given expression exactly at most `n` times
export %inline
atmost : (n : Nat) -> RExpOf True t -> RExpOf False t
atmost 0     x = eps
atmost (S k) x = opt (x >> atmost k x)

||| Repeats the given expression between `m` and `n`  times
export
repeatRange : (m,n : Nat) -> RExpOf True t -> RExpOf (rep m) t
repeatRange m n x = orF $ repeat m x >> atmost (n `minus` m) x

||| Repeats the given expression at least `n` times
export %inline
atleast : (n : Nat) -> RExpOf True t -> RExpOf (rep n) t
atleast n x = orF $ repeat n x >> star x

--------------------------------------------------------------------------------
-- Character Classes
--------------------------------------------------------------------------------

||| Accepts only the newline character
public export %inline
nl : RExp True
nl = '\n'

||| Accepts any character in the given range of unicode
||| code points.
|||
||| Please note that even if the given range exceeds the given
||| set of valid codepoints (0x000 - 0xD7FF || 0xE000 - 0x10FFFF),
||| it will be intersected with the valid set during generation
||| of the state machine.
public export %inline
range32 : Bits32 -> Bits32 -> RExp True
range32 x y = Ch (range $ range x y)

||| Accepts any character in the given range
public export %inline
range : Char -> Char -> RExp True
range x y = Ch (range $ charRange x y)

||| Accepts any character in the given range
public export %inline
digit : RExp True
digit = Ch digit

public export
posdigit : RExp True
posdigit = Ch posdigit

||| Accepts any upper case character
public export %inline
upper : RExp True
upper = Ch upper

||| Accepts any lower case character
public export %inline
lower : RExp True
lower = Ch lower

||| Accepts any alphabetic character
public export %inline
alpha : RExp True
alpha = Ch alpha

||| Accepts any alpha-numeric character
public export %inline
alphaNum : RExp True
alphaNum = Ch alphaNum

||| Accepts a binary digit ('0' or '1').
public export
bindigit : RExp True
bindigit = chr '0' <|> chr '1'

||| Accepts an octal digit.
public export
octdigit : RExp True
octdigit = range '0' '7'

||| Accepts a hexadecimal digit.
|||
||| Letters can be upper or lower case.
public export
hexdigit : RExp True
hexdigit = range '0' '9' <|> range 'a' 'f' <|> range 'A' 'F'

||| Accepts a single unicode control codepoint.
|||
||| Control characters are unicode codepoints in the ranges
||| 0x00 to 0x1f (`'\NUL'` to `'\US'`) and
||| 0x71 to 0x9f (`'\DEL'` to `'\159'`).
|||
||| Among these, the most commonly used are tab (`'\t'`, 0x09),
||| line feed (`'\r'`, 0x0d) and carriage return (`'\n'`, 0x0a).
public export %inline
control : RExp True
control = Ch control

||| Accepts a non-control unicode codepoint.
public export %inline
dot : RExp True
dot = Ch printable

||| Accepts an arbitrary number of printable unicode codepoints.
public export %inline
dots : RExp False
dots = star dot

||| Accepts a non-empty number of printable unicode codepoints.
public export %inline
dots1 : RExp True
dots1 = plus dot

--------------------------------------------------------------------------------
-- Integers
--------------------------------------------------------------------------------

||| Recognizes a non-empty string of binary digits.
public export
binary : RExp True
binary = plus bindigit

||| Recognizes a non-empty string of octal digits.
public export
octal : RExp True
octal = plus octdigit

||| Recognizes a non-empty string of decimal digits.
|||
||| In this case, no leading zeroes are allowed: "0" is recognized
||| but "01" is not.
public export
decimal : RExp True
decimal = chr '0' <|> (posdigit >> star digit)

||| Recognizes a non-empty string of hexadecimal digits.
|||
||| Letters can be upper or lower case.
public export
hexadecimal : RExp True
hexadecimal = plus hexdigit

||| Accepts a decimal number (like `decimal`: no leading zeroes)
||| prefixed with an optional "minus" sign.
public export
integer : RExp True
integer = opt '-' >> decimal

||| Accepts a natural number in binary, octal, decimal (no leading zeroes),
||| or hexadecimal form.
|||
||| Non-decimal forms must be prefixed with "0b" (binary), "0o" (octal), or
||| "0x" (hexadecimal), just like in Idris.
public export
natural : RExp True
natural =
  (like "0b" >> binary)      <|>
  (like "0o" >> octal)       <|>
  (like "0x" >> hexadecimal) <|>
  decimal

--------------------------------------------------------------------------------
-- Constant Size Expressions
--------------------------------------------------------------------------------

||| Proof that regular expression `x` consists of a constant number
||| (`n`) of characters.
public export
data ConstSize : (n : Nat) -> (x : RExpOf b t) -> Type where
  [search x]
  ||| The epsilon expression trivially matches zero characters.
  CS0   : ConstSize 0 Eps

  ||| A single character trivially matches one character.
  CSC   : ConstSize 1 (Ch x)

  ||| Sequencing two constant size expressions of `m` and `n` characters
  ||| yields an expression matching `m+n` characters.
  CSAnd : ConstSize m x -> ConstSize n y -> ConstSize (m+n) (And x y)

  ||| A choice of constant size expressions all matching the same number of
  ||| characters yields again an expression matching the same number of
  ||| characters.
  CSOr  : ConstSize n x -> ConstSize n y -> ConstSize n (Or x y)

||| Decides if the given expression matches a constant number of
||| characters.
export
constSize : (x : RExpOf b t) -> Maybe (Subset Nat (`ConstSize` x))
constSize Eps       = Just (Element 0 CS0)
constSize (Ch x)    = Just (Element 1 CSC)
constSize (And x y) = do
  Element m p1 <- constSize x
  Element n p2 <- constSize y
  pure (Element (m+n) (CSAnd p1 p2))
constSize (Or x y)  = do
  Element m p1 <- constSize x
  Element n p2 <- constSize y
  case hdecEq m n of
    Just0 prf => pure (Element m (CSOr p1 (rewrite prf in p2)))
    Nothing0  => Nothing
constSize (Star x)  = Nothing

||| Proof that the `chars cs` combinator returns an expression
||| that matches a constant number of `length cs` characters.
export
0 charsConstSize :
     (cs : List Char)
  -> {auto 0 prf : NonEmpty cs}
  -> ConstSize (length cs) (chars cs)
charsConstSize [c]              = CSC
charsConstSize (c :: cs@(_::_)) = CSAnd CSC (charsConstSize cs)

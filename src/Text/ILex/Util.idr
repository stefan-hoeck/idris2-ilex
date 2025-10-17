module Text.ILex.Util

import Data.ByteString
import Data.Linear.Ref1
import Derive.Prelude
import Syntax.T1
import Text.Bounds
import Text.ParseError
import Text.ILex.Parser
import Text.ILex.RExp

%default total

--------------------------------------------------------------------------------
-- Reading Numbers
--------------------------------------------------------------------------------

export %inline
decimaldigit : Bits8 -> Integer
decimaldigit x = cast x - 48

export
hexdigit : Bits8 -> Integer
hexdigit x =
  if      x <= byte_9 then cast x - cast byte_0
  else if x <= byte_F then 10 + cast x - cast byte_A
  else                     10 + cast x - cast byte_a

parameters (bv : ByteVect n)
  export
  binaryBV : Integer -> (k : Nat) -> (x : Ix k n) => Integer
  binaryBV res 0     = res
  binaryBV res (S k) =
      case ix bv k of
        48 => binaryBV (res * 2) k
        _  => binaryBV (res * 2 + 1) k

  export
  binarySepBV : Integer -> (k : Nat) -> (x : Ix k n) => Integer
  binarySepBV res 0     = res
  binarySepBV res (S k) =
      case ix bv k of
        48 => binarySepBV (res * 2) k
        49 => binarySepBV (res * 2 + 1) k
        _  => binarySepBV res k

  export
  octalBV : Integer -> (k : Nat) -> (x : Ix k n) => Integer
  octalBV res 0     = res
  octalBV res (S k) = octalBV (res * 8 + decimaldigit (ix bv k)) k

  export
  octalSepBV : Bits8 -> Integer -> (k : Nat) -> (x : Ix k n) => Integer
  octalSepBV sep res 0     = res
  octalSepBV sep res (S k) =
     let b := ix bv k
      in case prim__eq_Bits8 sep b of
           0 => octalSepBV sep (res * 8 + decimaldigit b) k
           _ => octalSepBV sep res k

  export
  decimalBV : Integer -> (k : Nat) -> (x : Ix k n) => Integer
  decimalBV res 0     = res
  decimalBV res (S k) = decimalBV (res * 10 + decimaldigit (ix bv k)) k

  export
  decimalSepBV : Bits8 -> Integer -> (k : Nat) -> (x : Ix k n) => Integer
  decimalSepBV sep res 0     = res
  decimalSepBV sep res (S k) =
     let b := ix bv k
      in case prim__eq_Bits8 sep b of
           0 => decimalSepBV sep (res * 10 + decimaldigit b) k
           _ => decimalSepBV sep res k

  export
  hexadecimalBV : Integer -> (k : Nat) -> (x : Ix k n) => Integer
  hexadecimalBV res 0     = res
  hexadecimalBV res (S k) = hexadecimalBV (res * 16 + hexdigit (ix bv k)) k

  export
  hexadecimalSepBV : Bits8 -> Integer -> (k : Nat) -> (x : Ix k n) => Integer
  hexadecimalSepBV sep res 0     = res
  hexadecimalSepBV sep res (S k) =
     let b := ix bv k
      in case prim__eq_Bits8 sep b of
           0 => hexadecimalSepBV sep (res * 16 + hexdigit b) k
           _ => hexadecimalSepBV sep res k

  export
  integerBV : (k : Nat) -> (x : Ix k n) => Integer
  integerBV 0     = 0
  integerBV (S k) =
    case ix bv k of
      45 => negate $ decimalBV 0 k       -- '-'
      43 => decimalBV 0 k                -- '+'
      b  => decimalBV (decimaldigit b) k

||| Converts a string of binary digits to an integer
export %inline
binary : ByteString -> Integer
binary (BS n bv) = binaryBV bv 0 n

||| Converts a string of binary digits containing optional
||| separators to an integer `0010_0011_1110_0011.
|||
||| Such integer literals are supported by Idris as well as TOML,
||| for instance:
export %inline
binarySep : ByteString -> Integer
binarySep (BS n bv) = binarySepBV bv 0 n

||| Converts a string of octal digits to an integer
export %inline
octal : ByteString -> Integer
octal (BS n bv) = octalBV bv 0 n

||| Converts a string of octal digits containing optional
||| separators to an integer `077_334`.
|||
||| Such integer literals are supported by Idris as well as TOML,
||| for instance:
export %inline
octalSep : Bits8 -> ByteString -> Integer
octalSep sep (BS n bv) = octalSepBV bv sep 0 n

||| Converts a string of decimal digits to an integer
export %inline
decimal : ByteString -> Integer
decimal (BS n bv) = decimalBV bv 0 n

||| Converts a string of decimal digits containing optional
||| separators to an integer `177_934`.
|||
||| Such integer literals are supported by Idris as well as TOML,
||| for instance:
export %inline
decimalSep : Bits8 -> ByteString -> Integer
decimalSep sep (BS n bv) = decimalSepBV bv sep 0 n

||| Converts a string of decimal digits to an integer
export %inline
hexadecimal : ByteString -> Integer
hexadecimal (BS n bv) = hexadecimalBV bv 0 n

||| Converts a string of decimal digits containing optional
||| separators to an integer `177_934`.
|||
||| Such integer literals are supported by Idris as well as TOML,
||| for instance:
export %inline
hexadecimalSep : Bits8 -> ByteString -> Integer
hexadecimalSep sep (BS n bv) = hexadecimalSepBV bv sep 0 n

||| Converts an integer literal with optional sign prefix
||| to an integer.
export %inline
integer : ByteString -> Integer
integer (BS n bv) = integerBV bv n

--------------------------------------------------------------------------------
-- Operator Precedence
--------------------------------------------------------------------------------

||| Utility for combining a snoc-list of expressions combined
||| via left-binding operators of different fixity into a single
||| expression.
export
mergeL : Ord o => (o -> e -> e -> e) -> SnocList (e,o) -> e -> e
mergeL merge sp y =
  case sp <>> [] of
    []        => y
    (x,ox)::t => go [<] x ox t y

  where
    app : SnocList (e,o) -> e -> o -> List (e,o) -> e -> e

    go : SnocList (e,o) -> e -> o -> List (e,o) -> e -> e
    go sx x ox []        z =
      case sx of
        [<]        => merge ox x z
        sp:<(w,ow) => go sp w ow [] (merge ox x z)

    go sx x ox ((y,oy) :: xs) z =
      case compare ox oy of
        LT => go (sx:<(x,ox)) y oy xs z
        EQ => go sx (merge ox x y) oy xs z
        GT => app sx (merge ox x y) oy xs z

    app [<]                x ox xs z = go [<] x ox xs z
    app outer@(sp:<(w,ow)) x ox xs z =
      case compare ow ox of
        LT => go outer x ox xs z
        _  => app sp (merge ow w x) ox xs z

||| Utility for converting a snoc list into a list.
|||
||| This is useful when streaming chunks of data and emitting
||| all the accumulated values of a single chunk.
export
maybeList : SnocList a -> Maybe (List a)
maybeList [<] = Nothing
maybeList sx  = Just (sx <>> [])

||| Concatenates the strings accumulated in a snoc list.
|||
||| This is a utility often used when lexing or parsing
||| string literals that support various kinds of escape
||| sequences.
export
snocPack : SnocList String -> String
snocPack [<]  = ""
snocPack [<s] = s
snocPack ss   = fastConcat $ ss <>> []

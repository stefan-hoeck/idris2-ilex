module Text.ILex.Util

import Data.ByteString
import Data.Linear.Ref1
import Derive.Prelude
import Syntax.T1
import Text.ILex.Bounds
import Text.ILex.Error
import Text.ILex.Parser
import Text.ILex.RExp

%hide Prelude.(>>=)
%hide Prelude.(>>)
%default total

--------------------------------------------------------------------------------
-- Reading Numbers
--------------------------------------------------------------------------------

||| Converts a string of binary digits to an integer
export
binary : ByteString -> Integer
binary (BS n bv) = go 0 n
  where
    go : Integer -> (k : Nat) -> (x : Ix k n) => Integer
    go res 0     = res
    go res (S k) =
      case ix bv k of
        48 => go (res * 2) k
        _  => go (res * 2 + 1) k

export %inline
decimaldigit : Bits8 -> Integer
decimaldigit x = cast x - 48

||| Converts a string of octal digits to an integer
export
octal : ByteString -> Integer
octal (BS n bv) = go 0 n
  where
    go : Integer -> (k : Nat) -> (x : Ix k n) => Integer
    go res 0     = res
    go res (S k) = go (res * 8 + decimaldigit (ix bv k)) k

||| Converts a string of decimal digits to an integer
export
decimal : ByteString -> Integer
decimal (BS n bv) = go 0 n
  where
    go : Integer -> (k : Nat) -> (x : Ix k n) => Integer
    go res 0     = res
    go res (S k) = go (res * 10 + decimaldigit (ix bv k)) k

export
hexdigit : Bits8 -> Integer
hexdigit x =
  if      x <= byte_9 then cast x - cast byte_0
  else if x <= byte_F then 10 + cast x - cast byte_A
  else                     10 + cast x - cast byte_a

||| Converts a string of decimal digits to an integer
export
hexadecimal : ByteString -> Integer
hexadecimal (BS n bv) = go 0 n
  where
    go : Integer -> (k : Nat) -> (x : Ix k n) => Integer
    go res 0     = res
    go res (S k) = go (res * 16 + hexdigit (ix bv k)) k

||| Converts an integer literal with optional sign prefix
||| to an integer.
export
integer : ByteString -> Integer
integer bs@(BS (S k) bv) =
  case bv `at` 0 of
    45 => negate $ decimal (BS k $ tail bv)
    43 => decimal (BS k $ tail bv)
    _  => decimal bs
integer bs = decimal bs

--------------------------------------------------------------------------------
-- Encodings
--------------------------------------------------------------------------------

||| Converts an integer to a hexadecimal digit.
|||
||| This assumes that the integer is already in the range 0 - 15.
public export
hexChar : Integer -> Char
hexChar 0 = '0'
hexChar 1 = '1'
hexChar 2 = '2'
hexChar 3 = '3'
hexChar 4 = '4'
hexChar 5 = '5'
hexChar 6 = '6'
hexChar 7 = '7'
hexChar 8 = '8'
hexChar 9 = '9'
hexChar 10 = 'a'
hexChar 11 = 'b'
hexChar 12 = 'c'
hexChar 13 = 'd'
hexChar 14 = 'e'
hexChar _  = 'f'

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

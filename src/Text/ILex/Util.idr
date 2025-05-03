module Text.ILex.Util

import Data.ByteString

%default total

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

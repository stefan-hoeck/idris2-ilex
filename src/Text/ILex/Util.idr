module Text.ILex.Util

import Derive.Prelude

%default total
%language ElabReflection

public export
toDigit : Char -> Integer
toDigit '0' = 0
toDigit '1' = 1
toDigit '2' = 2
toDigit '3' = 3
toDigit '4' = 4
toDigit '5' = 5
toDigit '6' = 6
toDigit '7' = 7
toDigit '8' = 8
toDigit _   = 9

public export
toHex : Char -> Integer
toHex 'a' = 10
toHex 'b' = 11
toHex 'c' = 12
toHex 'd' = 13
toHex 'e' = 14
toHex _   = 15

public export
toHexDigit : Char -> Integer
toHexDigit c =
  case isDigit c of
    True  => toDigit c
    False => toHex (toLower c)

public export
data LexErr : Type where
  EOI        : LexErr
  Unexpected : Char -> LexErr

%runElab derive "LexErr" [Show,Eq]

public export
record Pos where
  constructor P
  row : Nat
  col : Nat

%runElab derive "Pos" [Show,Eq,Ord]

public export
record WBounds a where
  constructor WB
  start : Pos
  val   : a
  end   : Pos

%runElab derive "WBounds" [Show,Eq]

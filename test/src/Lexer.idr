module Lexer

import Text.ILex.Util

%default total

public export
lexNat : String -> Either LexErr (SnocList Integer)

public export
lexNat1 : List Char -> Nat -> Nat -> Either LexErr (SnocList Integer)

public export
lexNat2 : List Char -> Nat -> Nat -> Either LexErr (SnocList Integer)

public export
lexNat3 : List Char -> Nat -> Nat -> Integer -> Either LexErr (SnocList Integer)

public export
lexNat4 : List Char -> Nat -> Nat -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat5 : List Char -> Nat -> Nat -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat6 : List Char -> Nat -> Nat -> Either LexErr (SnocList Integer)

public export
lexNat7 : List Char -> Nat -> Nat -> Either LexErr (SnocList Integer)

public export
lexNat8 : List Char -> Nat -> Nat -> Either LexErr (SnocList Integer)

public export
lexNat9 : List Char -> Nat -> Nat -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat10 : List Char -> Nat -> Nat -> Integer -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat11 : List Char -> Nat -> Nat -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat12 : List Char -> Nat -> Nat -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat13 : List Char -> Nat -> Nat -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat14 : List Char -> Nat -> Nat -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat15 : List Char -> Nat -> Nat -> Integer -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat16 : List Char -> Nat -> Nat -> Integer -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat17 : List Char -> Nat -> Nat -> Integer -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat18 : List Char -> Nat -> Nat -> Integer -> Either LexErr (SnocList Integer)

public export
lexNat19 : List Char -> Nat -> Nat -> Integer -> Either LexErr (SnocList Integer)

public export
lexNat20 : List Char -> Nat -> Nat -> Integer -> Either LexErr (SnocList Integer)

lexNat s = lexNat1 (unpack s) 0 0

lexNat1 str@(c::cs) row col =
  case c of
    '0' => lexNat2 cs row (S col)
    _  => case (&&) ((<=) c '9') ((<=) '1' c) of
      True => lexNat3 cs row (S col) (toDigit c)
      _   => Left (cast (Unexpected c))
lexNat1 [] row col = Left (cast EOI)

lexNat2 str@(c::cs) row col =
  case c of
    ',' => lexNat5 cs row (S col) ((:<) Lin 0)
    'b' => lexNat6 cs row (S col)
    'o' => lexNat7 cs row (S col)
    'x' => lexNat8 cs row (S col)
    _   => lexNat4 str row col ((:<) Lin 0)
lexNat2 [] row col = lexNat4 Nil row col ((:<) Lin 0)

lexNat3 str@(c::cs) row col x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat3 cs row (S col) ((+) ((*) x0 10) (toDigit c))
    _    => lexNat11 str row col ((:<) Lin x0)
lexNat3 [] row col x0 = lexNat11 Nil row col ((:<) Lin x0)

lexNat4 str@(c::cs) row col x0 = Left (Unexpected c)
lexNat4 [] row col x0 = Right x0

lexNat5 str@(c::cs) row col x0 =
  case c of
    '0' => lexNat9 cs row (S col) x0
    _  => case (&&) ((<=) c '9') ((<=) '1' c) of
      True => lexNat10 cs row (S col) (toDigit c) x0
      _   => Left (cast (Unexpected c))
lexNat5 [] row col x0 = Left (cast EOI)

lexNat6 str@(c::cs) row col =
  case (&&) ((<=) c '1') ((<=) '0' c) of
    True => lexNat18 cs row (S col) (toDigit c)
    _    => Left (cast (Unexpected c))
lexNat6 [] row col = Left (cast EOI)

lexNat7 str@(c::cs) row col =
  case (&&) ((<=) c '7') ((<=) '0' c) of
    True => lexNat19 cs row (S col) (toDigit c)
    _    => Left (cast (Unexpected c))
lexNat7 [] row col = Left (cast EOI)

lexNat8 str@(c::cs) row col =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat20 cs row (S col) (toDigit c)
    _    =>
      case (&&) ((<=) c 'F') ((<=) 'A' c) of
        True => lexNat20 cs row (S col) (toHex (toLower c))
        _    =>
          case (&&) ((<=) c 'f') ((<=) 'a' c) of
            True => lexNat20 cs row (S col) (toHex c)
            _    => Left (cast (Unexpected c))
lexNat8 [] row col = Left (cast EOI)

lexNat9 str@(c::cs) row col x0 =
  case c of
    'b' => lexNat12 cs row (S col) x0
    'o' => lexNat13 cs row (S col) x0
    'x' => lexNat14 cs row (S col) x0
    _   => lexNat11 str row col ((:<) x0 0)
lexNat9 [] row col x0 = lexNat11 Nil row col ((:<) x0 0)

lexNat10 str@(c::cs) row col x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat10 cs row (S col) ((+) ((*) x1 10) (toDigit c)) x0
    _    => lexNat11 str row col ((:<) x0 x1)
lexNat10 [] row col x1 x0 = lexNat11 Nil row col ((:<) x0 x1)

lexNat11 str@(c::cs) row col x0 =
  case c of
    ',' => lexNat5 cs row (S col) x0
    _   => lexNat4 str row col x0
lexNat11 [] row col x0 = lexNat4 Nil row col x0

lexNat12 str@(c::cs) row col x0 =
  case (&&) ((<=) c '1') ((<=) '0' c) of
    True => lexNat15 cs row (S col) (toDigit c) x0
    _    => Left (cast (Unexpected c))
lexNat12 [] row col x0 = Left (cast EOI)

lexNat13 str@(c::cs) row col x0 =
  case (&&) ((<=) c '7') ((<=) '0' c) of
    True => lexNat16 cs row (S col) (toDigit c) x0
    _    => Left (cast (Unexpected c))
lexNat13 [] row col x0 = Left (cast EOI)

lexNat14 str@(c::cs) row col x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat17 cs row (S col) (toDigit c) x0
    _    =>
      case (&&) ((<=) c 'F') ((<=) 'A' c) of
        True => lexNat17 cs row (S col) (toHex (toLower c)) x0
        _    =>
          case (&&) ((<=) c 'f') ((<=) 'a' c) of
            True => lexNat17 cs row (S col) (toHex c) x0
            _    => Left (cast (Unexpected c))
lexNat14 [] row col x0 = Left (cast EOI)

lexNat15 str@(c::cs) row col x1 x0 =
  case (&&) ((<=) c '1') ((<=) '0' c) of
    True => lexNat15 cs row (S col) ((+) ((*) x1 2) (toDigit c)) x0
    _    => lexNat11 str row col ((:<) x0 x1)
lexNat15 [] row col x1 x0 = lexNat11 Nil row col ((:<) x0 x1)

lexNat16 str@(c::cs) row col x1 x0 =
  case (&&) ((<=) c '7') ((<=) '0' c) of
    True => lexNat16 cs row (S col) ((+) ((*) x1 8) (toDigit c)) x0
    _    => lexNat11 str row col ((:<) x0 x1)
lexNat16 [] row col x1 x0 = lexNat11 Nil row col ((:<) x0 x1)

lexNat17 str@(c::cs) row col x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat17 cs row (S col) ((+) ((*) x1 16) (toDigit c)) x0
    _    =>
      case (&&) ((<=) c 'F') ((<=) 'A' c) of
        True => lexNat17 cs row (S col) ((+) ((*) x1 16) (toHex (toLower c))) x0
        _    =>
          case (&&) ((<=) c 'f') ((<=) 'a' c) of
            True => lexNat17 cs row (S col) ((+) ((*) x1 16) (toHex c)) x0
            _    => lexNat11 str row col ((:<) x0 x1)
lexNat17 [] row col x1 x0 = lexNat11 Nil row col ((:<) x0 x1)

lexNat18 str@(c::cs) row col x0 =
  case (&&) ((<=) c '1') ((<=) '0' c) of
    True => lexNat18 cs row (S col) ((+) ((*) x0 2) (toDigit c))
    _    => lexNat11 str row col ((:<) Lin x0)
lexNat18 [] row col x0 = lexNat11 Nil row col ((:<) Lin x0)

lexNat19 str@(c::cs) row col x0 =
  case (&&) ((<=) c '7') ((<=) '0' c) of
    True => lexNat19 cs row (S col) ((+) ((*) x0 8) (toDigit c))
    _    => lexNat11 str row col ((:<) Lin x0)
lexNat19 [] row col x0 = lexNat11 Nil row col ((:<) Lin x0)

lexNat20 str@(c::cs) row col x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat20 cs row (S col) ((+) ((*) x0 16) (toDigit c))
    _    =>
      case (&&) ((<=) c 'F') ((<=) 'A' c) of
        True => lexNat20 cs row (S col) ((+) ((*) x0 16) (toHex (toLower c)))
        _    =>
          case (&&) ((<=) c 'f') ((<=) 'a' c) of
            True => lexNat20 cs row (S col) ((+) ((*) x0 16) (toHex c))
            _    => lexNat11 str row col ((:<) Lin x0)
lexNat20 [] row col x0 = lexNat11 Nil row col ((:<) Lin x0)



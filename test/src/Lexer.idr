module Lexer

import Text.ILex.Util

%default total

public export
lexNat : String -> Either LexErr (SnocList Integer)

public export
lexNat1 : List Char -> Either LexErr (SnocList Integer)

public export
lexNat2 : List Char -> Either LexErr (SnocList Integer)

public export
lexNat3 : List Char -> Integer -> Either LexErr (SnocList Integer)

public export
lexNat4 : List Char -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat5 : List Char -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat6 : List Char -> Either LexErr (SnocList Integer)

public export
lexNat7 : List Char -> Either LexErr (SnocList Integer)

public export
lexNat8 : List Char -> Either LexErr (SnocList Integer)

public export
lexNat9 : List Char -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat10 : List Char -> Integer -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat11 : List Char -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat12 : List Char -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat13 : List Char -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat14 : List Char -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat15 : List Char -> Integer -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat16 : List Char -> Integer -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat17 : List Char -> Integer -> SnocList Integer -> Either LexErr (SnocList Integer)

public export
lexNat18 : List Char -> Integer -> Either LexErr (SnocList Integer)

public export
lexNat19 : List Char -> Integer -> Either LexErr (SnocList Integer)

public export
lexNat20 : List Char -> Integer -> Either LexErr (SnocList Integer)

lexNat = lexNat1 . unpack
lexNat1 str@(c::cs) =
  case c of
    '0' => lexNat2 cs
    _  => case (&&) ((<=) c '9') ((<=) '1' c) of
      True => lexNat3 cs (toDigit c)
      _   => Left (cast (Unexpected c))
lexNat1 [] = Left (cast EOI)

lexNat2 str@(c::cs) =
  case c of
    ',' => lexNat5 cs ((:<) Lin 0)
    'b' => lexNat6 cs
    'o' => lexNat7 cs
    'x' => lexNat8 cs
    _   => lexNat4 str ((:<) Lin 0)
lexNat2 [] = lexNat4 Nil ((:<) Lin 0)

lexNat3 str@(c::cs) x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat3 cs ((+) ((*) x0 10) (toDigit c))
    _    => lexNat11 str ((:<) Lin x0)
lexNat3 [] x0 = lexNat11 Nil ((:<) Lin x0)

lexNat4 str@(c::cs) x0 = Left (Unexpected c)
lexNat4 [] x0 = Right x0

lexNat5 str@(c::cs) x0 =
  case c of
    '0' => lexNat9 cs x0
    _  => case (&&) ((<=) c '9') ((<=) '1' c) of
      True => lexNat10 cs (toDigit c) x0
      _   => Left (cast (Unexpected c))
lexNat5 [] x0 = Left (cast EOI)

lexNat6 str@(c::cs) =
  case (&&) ((<=) c '1') ((<=) '0' c) of
    True => lexNat18 cs (toDigit c)
    _    => Left (cast (Unexpected c))
lexNat6 [] = Left (cast EOI)

lexNat7 str@(c::cs) =
  case (&&) ((<=) c '7') ((<=) '0' c) of
    True => lexNat19 cs (toDigit c)
    _    => Left (cast (Unexpected c))
lexNat7 [] = Left (cast EOI)

lexNat8 str@(c::cs) =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat20 cs (toDigit c)
    _    =>
      case (&&) ((<=) c 'F') ((<=) 'A' c) of
        True => lexNat20 cs (toHex (toLower c))
        _    =>
          case (&&) ((<=) c 'f') ((<=) 'a' c) of
            True => lexNat20 cs (toHex c)
            _    => Left (cast (Unexpected c))
lexNat8 [] = Left (cast EOI)

lexNat9 str@(c::cs) x0 =
  case c of
    'b' => lexNat12 cs x0
    'o' => lexNat13 cs x0
    'x' => lexNat14 cs x0
    _   => lexNat11 str ((:<) x0 0)
lexNat9 [] x0 = lexNat11 Nil ((:<) x0 0)

lexNat10 str@(c::cs) x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat10 cs ((+) ((*) x1 10) (toDigit c)) x0
    _    => lexNat11 str ((:<) x0 x1)
lexNat10 [] x1 x0 = lexNat11 Nil ((:<) x0 x1)

lexNat11 str@(c::cs) x0 =
  case c of
    ',' => lexNat5 cs x0
    _   => lexNat4 str x0
lexNat11 [] x0 = lexNat4 Nil x0

lexNat12 str@(c::cs) x0 =
  case (&&) ((<=) c '1') ((<=) '0' c) of
    True => lexNat15 cs (toDigit c) x0
    _    => Left (cast (Unexpected c))
lexNat12 [] x0 = Left (cast EOI)

lexNat13 str@(c::cs) x0 =
  case (&&) ((<=) c '7') ((<=) '0' c) of
    True => lexNat16 cs (toDigit c) x0
    _    => Left (cast (Unexpected c))
lexNat13 [] x0 = Left (cast EOI)

lexNat14 str@(c::cs) x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat17 cs (toDigit c) x0
    _    =>
      case (&&) ((<=) c 'F') ((<=) 'A' c) of
        True => lexNat17 cs (toHex (toLower c)) x0
        _    =>
          case (&&) ((<=) c 'f') ((<=) 'a' c) of
            True => lexNat17 cs (toHex c) x0
            _    => Left (cast (Unexpected c))
lexNat14 [] x0 = Left (cast EOI)

lexNat15 str@(c::cs) x1 x0 =
  case (&&) ((<=) c '1') ((<=) '0' c) of
    True => lexNat15 cs ((+) ((*) x1 2) (toDigit c)) x0
    _    => lexNat11 str ((:<) x0 x1)
lexNat15 [] x1 x0 = lexNat11 Nil ((:<) x0 x1)

lexNat16 str@(c::cs) x1 x0 =
  case (&&) ((<=) c '7') ((<=) '0' c) of
    True => lexNat16 cs ((+) ((*) x1 8) (toDigit c)) x0
    _    => lexNat11 str ((:<) x0 x1)
lexNat16 [] x1 x0 = lexNat11 Nil ((:<) x0 x1)

lexNat17 str@(c::cs) x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat17 cs ((+) ((*) x1 16) (toDigit c)) x0
    _    =>
      case (&&) ((<=) c 'F') ((<=) 'A' c) of
        True => lexNat17 cs ((+) ((*) x1 16) (toHex (toLower c))) x0
        _    =>
          case (&&) ((<=) c 'f') ((<=) 'a' c) of
            True => lexNat17 cs ((+) ((*) x1 16) (toHex c)) x0
            _    => lexNat11 str ((:<) x0 x1)
lexNat17 [] x1 x0 = lexNat11 Nil ((:<) x0 x1)

lexNat18 str@(c::cs) x0 =
  case (&&) ((<=) c '1') ((<=) '0' c) of
    True => lexNat18 cs ((+) ((*) x0 2) (toDigit c))
    _    => lexNat11 str ((:<) Lin x0)
lexNat18 [] x0 = lexNat11 Nil ((:<) Lin x0)

lexNat19 str@(c::cs) x0 =
  case (&&) ((<=) c '7') ((<=) '0' c) of
    True => lexNat19 cs ((+) ((*) x0 8) (toDigit c))
    _    => lexNat11 str ((:<) Lin x0)
lexNat19 [] x0 = lexNat11 Nil ((:<) Lin x0)

lexNat20 str@(c::cs) x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat20 cs ((+) ((*) x0 16) (toDigit c))
    _    =>
      case (&&) ((<=) c 'F') ((<=) 'A' c) of
        True => lexNat20 cs ((+) ((*) x0 16) (toHex (toLower c)))
        _    =>
          case (&&) ((<=) c 'f') ((<=) 'a' c) of
            True => lexNat20 cs ((+) ((*) x0 16) (toHex c))
            _    => lexNat11 str ((:<) Lin x0)
lexNat20 [] x0 = lexNat11 Nil ((:<) Lin x0)



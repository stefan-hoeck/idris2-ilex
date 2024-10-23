module PackageLexer

import Text.ILex.Util
import Package

%default total

public export
lexTok : String -> Either LexErr (SnocList Token)

public export
lexTok1 : List Char -> Either LexErr (SnocList Token)

public export
lexTok2 : List Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok3 : List Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok4 : List Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok5 : List Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok6 : List Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok7 : List Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok8 : List Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok9 : List Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok10 : List Char -> SnocList Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok11 : List Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok12 : List Char -> Integer -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok13 : List Char -> SnocList Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok14 : List Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok15 : List Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok16 : List Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok17 : List Char -> Integer -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok18 : List Char -> Integer -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok19 : List Char -> Integer -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok20 : List Char -> SnocList String -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok21 : List Char -> SnocList String -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok22 : List Char -> SnocList Char -> SnocList String -> SnocList Token -> Either LexErr (SnocList Token)

lexTok = lexTok1 . unpack

lexTok1 str = lexTok2 str Lin
lexTok2 str@(c::cs) x0 =
  case c of
    '&' => lexTok4 cs x0
    '-' => lexTok5 cs x0
    '.' => lexTok2 cs ((:<) x0 Dot)
    '0' => lexTok6 cs x0
    '<' => lexTok7 cs x0
    '=' => lexTok8 cs x0
    '>' => lexTok9 cs x0
    _  => case isIdentStart c of
      True => lexTok10 cs ((:<) Lin c) x0
      _  => case isSpace c of
        True => lexTok11 cs x0
        _  => case (&&) ((<=) c '9') ((<=) '1' c) of
          True => lexTok12 cs (toDigit c) x0
          _   => lexTok3 str x0
lexTok2 [] x0 = lexTok3 Nil x0

lexTok3 str@(c::cs) x0 = Left (Unexpected c)
lexTok3 [] x0 = Right x0

lexTok4 str@(c::cs) x0 =
  case c of
    '&' => lexTok2 cs ((:<) x0 AndOp)
    _   => Left (cast (Unexpected c))
lexTok4 [] x0 = Left (cast EOI)

lexTok5 str@(c::cs) x0 =
  case c of
    '-' => lexTok13 cs Lin x0
    _   => Left (cast (Unexpected c))
lexTok5 [] x0 = Left (cast EOI)

lexTok6 str@(c::cs) x0 =
  case c of
    'b' => lexTok14 cs x0
    'o' => lexTok15 cs x0
    'x' => lexTok16 cs x0
    _   => lexTok2 str ((:<) x0 (IntegerLit 0))
lexTok6 [] x0 = lexTok2 Nil ((:<) x0 (IntegerLit 0))

lexTok7 str@(c::cs) x0 =
  case c of
    '=' => lexTok2 cs ((:<) x0 LTE)
    _   => lexTok2 str ((:<) x0 LT)
lexTok7 [] x0 = lexTok2 Nil ((:<) x0 LT)

lexTok8 str@(c::cs) x0 =
  case c of
    '=' => lexTok2 cs ((:<) x0 EqOp)
    _   => lexTok2 str ((:<) x0 Equals)
lexTok8 [] x0 = lexTok2 Nil ((:<) x0 Equals)

lexTok9 str@(c::cs) x0 =
  case c of
    '=' => lexTok2 cs ((:<) x0 GTE)
    _   => lexTok2 str ((:<) x0 GT)
lexTok9 [] x0 = lexTok2 Nil ((:<) x0 GT)

lexTok10 str@(c::cs) x1 x0 =
  case isIdentTrailing c of
    True => lexTok10 cs ((:<) x1 c) x0
    _    => lexTok20 str ((:<) Lin (pack ((<>>) x1 Nil))) x0
lexTok10 [] x1 x0 = lexTok20 Nil ((:<) Lin (pack ((<>>) x1 Nil))) x0

lexTok11 str@(c::cs) x0 =
  case isSpace c of
    True => lexTok11 cs x0
    _    => lexTok2 str ((:<) x0 Space)
lexTok11 [] x0 = lexTok2 Nil ((:<) x0 Space)

lexTok12 str@(c::cs) x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexTok12 cs ((+) ((*) x1 10) (toDigit c)) x0
    _    => lexTok2 str ((:<) x0 (IntegerLit x1))
lexTok12 [] x1 x0 = lexTok2 Nil ((:<) x0 (IntegerLit x1))

lexTok13 str@(c::cs) x1 x0 =
  case (/=) c (fromChar '\n') of
    True => lexTok13 cs ((:<) x1 c) x0
    _    => lexTok2 str ((:<) x0 (comment x1))
lexTok13 [] x1 x0 = lexTok2 Nil ((:<) x0 (comment x1))

lexTok14 str@(c::cs) x0 =
  case (&&) ((<=) c '1') ((<=) '0' c) of
    True => lexTok17 cs (toDigit c) x0
    _    => Left (cast (Unexpected c))
lexTok14 [] x0 = Left (cast EOI)

lexTok15 str@(c::cs) x0 =
  case (&&) ((<=) c '7') ((<=) '0' c) of
    True => lexTok18 cs (toDigit c) x0
    _    => Left (cast (Unexpected c))
lexTok15 [] x0 = Left (cast EOI)

lexTok16 str@(c::cs) x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexTok19 cs (toDigit c) x0
    _    =>
      case (&&) ((<=) c 'F') ((<=) 'A' c) of
        True => lexTok19 cs (toHex (toLower c)) x0
        _    =>
          case (&&) ((<=) c 'f') ((<=) 'a' c) of
            True => lexTok19 cs (toHex c) x0
            _    => Left (cast (Unexpected c))
lexTok16 [] x0 = Left (cast EOI)

lexTok17 str@(c::cs) x1 x0 =
  case (&&) ((<=) c '1') ((<=) '0' c) of
    True => lexTok17 cs ((+) ((*) x1 2) (toDigit c)) x0
    _    => lexTok2 str ((:<) x0 (IntegerLit x1))
lexTok17 [] x1 x0 = lexTok2 Nil ((:<) x0 (IntegerLit x1))

lexTok18 str@(c::cs) x1 x0 =
  case (&&) ((<=) c '7') ((<=) '0' c) of
    True => lexTok18 cs ((+) ((*) x1 8) (toDigit c)) x0
    _    => lexTok2 str ((:<) x0 (IntegerLit x1))
lexTok18 [] x1 x0 = lexTok2 Nil ((:<) x0 (IntegerLit x1))

lexTok19 str@(c::cs) x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexTok19 cs ((+) ((*) x1 16) (toDigit c)) x0
    _    =>
      case (&&) ((<=) c 'F') ((<=) 'A' c) of
        True => lexTok19 cs ((+) ((*) x1 16) (toHex (toLower c))) x0
        _    =>
          case (&&) ((<=) c 'f') ((<=) 'a' c) of
            True => lexTok19 cs ((+) ((*) x1 16) (toHex c)) x0
            _    => lexTok2 str ((:<) x0 (IntegerLit x1))
lexTok19 [] x1 x0 = lexTok2 Nil ((:<) x0 (IntegerLit x1))

lexTok20 str@(c::cs) x1 x0 =
  case c of
    '.' => lexTok21 cs x1 x0
    _   => lexTok2 str ((:<) x0 (fromIdents x1))
lexTok20 [] x1 x0 = lexTok2 Nil ((:<) x0 (fromIdents x1))

lexTok21 str@(c::cs) x1 x0 =
  case isIdentStart c of
    True => lexTok22 cs ((:<) Lin c) x1 x0
    _    => Left (cast (Unexpected c))
lexTok21 [] x1 x0 = Left (cast EOI)

lexTok22 str@(c::cs) x2 x1 x0 =
  case isIdentTrailing c of
    True => lexTok22 cs ((:<) x2 c) x1 x0
    _    => lexTok20 str ((:<) x1 (pack ((<>>) x2 Nil))) x0
lexTok22 [] x2 x1 x0 = lexTok20 Nil ((:<) x1 (pack ((<>>) x2 Nil))) x0



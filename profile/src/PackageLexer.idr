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
lexTok4 : List Char -> SnocList Char -> SnocList Token -> Either LexErr (SnocList Token)

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
lexTok11 : List Char -> SnocList Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok12 : List Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok13 : List Char -> Integer -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok14 : List Char -> SnocList Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok15 : List Char -> SnocList Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok16 : List Char -> SnocList Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok17 : List Char -> Integer -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok18 : List Char -> SnocList String -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok19 : List Char -> SnocList String -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok20 : List Char -> SnocList Char -> SnocList String -> SnocList Token -> Either LexErr (SnocList Token)

lexTok = lexTok1 . unpack

lexTok1 str = lexTok2 str Lin
lexTok2 str@(c::cs) x0 =
  case c of
    '"' => lexTok4 cs Lin x0
    '&' => lexTok5 cs x0
    ',' => lexTok2 cs ((:<) x0 Separator)
    '-' => lexTok6 cs x0
    '.' => lexTok2 cs ((:<) x0 Dot)
    '0' => lexTok2 cs ((:<) x0 (IntegerLit 0))
    '<' => lexTok7 cs x0
    '=' => lexTok8 cs x0
    '>' => lexTok9 cs x0
    _  => case isIdentStart c of
      True => lexTok10 cs ((:<) Lin c) x0
      _  => case isLower c of
        True => lexTok11 cs ((:<) Lin c) x0
        _  => case isSpace c of
          True => lexTok12 cs x0
          _  => case (&&) ((<=) c '9') ((<=) '1' c) of
            True => lexTok13 cs (toDigit c) x0
            _   => lexTok3 str x0
lexTok2 [] x0 = lexTok3 Nil x0

lexTok3 str@(c::cs) x0 = Left (Unexpected c)
lexTok3 [] x0 = Right x0

lexTok4 str@(c::cs) x1 x0 =
  case c of
    '\\' => lexTok15 cs x1 x0
    _  => case validStrChar c of
      True => lexTok4 cs ((:<) x1 c) x0
      _   => lexTok14 str x1 x0
lexTok4 [] x1 x0 = lexTok14 Nil x1 x0

lexTok5 str@(c::cs) x0 =
  case c of
    '&' => lexTok2 cs ((:<) x0 AndOp)
    _   => Left (cast (Unexpected c))
lexTok5 [] x0 = Left (cast EOI)

lexTok6 str@(c::cs) x0 =
  case c of
    '-' => lexTok16 cs Lin x0
    '0' => lexTok2 cs ((:<) x0 (IntegerLit (negate 0)))
    _  => case (&&) ((<=) c '9') ((<=) '1' c) of
      True => lexTok17 cs (toDigit c) x0
      _   => Left (cast (Unexpected c))
lexTok6 [] x0 = Left (cast EOI)

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
    _    => lexTok18 str ((:<) Lin (pack ((<>>) x1 Nil))) x0
lexTok10 [] x1 x0 = lexTok18 Nil ((:<) Lin (pack ((<>>) x1 Nil))) x0

lexTok11 str@(c::cs) x1 x0 =
  case isIdentTrailing c of
    True => lexTok11 cs ((:<) x1 c) x0
    _    => lexTok2 str ((:<) x0 (PkgName (pack ((<>>) x1 Nil))))
lexTok11 [] x1 x0 = lexTok2 Nil ((:<) x0 (PkgName (pack ((<>>) x1 Nil))))

lexTok12 str@(c::cs) x0 =
  case isSpace c of
    True => lexTok12 cs x0
    _    => lexTok2 str ((:<) x0 Space)
lexTok12 [] x0 = lexTok2 Nil ((:<) x0 Space)

lexTok13 str@(c::cs) x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexTok13 cs ((+) ((*) x1 10) (toDigit c)) x0
    _    => lexTok2 str ((:<) x0 (IntegerLit x1))
lexTok13 [] x1 x0 = lexTok2 Nil ((:<) x0 (IntegerLit x1))

lexTok14 str@(c::cs) x1 x0 =
  case c of
    '"' => lexTok2 cs ((:<) x0 (StringLit (pack ((<>>) x1 Nil))))
    _   => Left (cast (Unexpected c))
lexTok14 [] x1 x0 = Left (cast EOI)

lexTok15 str@(c::cs) x1 x0 =
  case (/=) c (fromChar '\n') of
    True => lexTok4 cs ((:<) x1 c) x0
    _    => Left (cast (Unexpected c))
lexTok15 [] x1 x0 = Left (cast EOI)

lexTok16 str@(c::cs) x1 x0 =
  case (/=) c (fromChar '\n') of
    True => lexTok16 cs ((:<) x1 c) x0
    _    => lexTok2 str ((:<) x0 (comment x1))
lexTok16 [] x1 x0 = lexTok2 Nil ((:<) x0 (comment x1))

lexTok17 str@(c::cs) x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexTok17 cs ((+) ((*) x1 10) (toDigit c)) x0
    _    => lexTok2 str ((:<) x0 (IntegerLit (negate x1)))
lexTok17 [] x1 x0 = lexTok2 Nil ((:<) x0 (IntegerLit (negate x1)))

lexTok18 str@(c::cs) x1 x0 =
  case c of
    '.' => lexTok19 cs x1 x0
    _   => lexTok2 str ((:<) x0 (module' x1))
lexTok18 [] x1 x0 = lexTok2 Nil ((:<) x0 (module' x1))

lexTok19 str@(c::cs) x1 x0 =
  case isIdentStart c of
    True => lexTok20 cs ((:<) Lin c) x1 x0
    _    => Left (cast (Unexpected c))
lexTok19 [] x1 x0 = Left (cast EOI)

lexTok20 str@(c::cs) x2 x1 x0 =
  case isIdentTrailing c of
    True => lexTok20 cs ((:<) x2 c) x1 x0
    _    => lexTok18 str ((:<) x1 (pack ((<>>) x2 Nil))) x0
lexTok20 [] x2 x1 x0 = lexTok18 Nil ((:<) x1 (pack ((<>>) x2 Nil))) x0



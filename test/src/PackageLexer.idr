module PackageLexer

import Text.ILex.Util
import Package

%default total

public export
lexTok : String -> Either LexErr (SnocList Token)

public export
lexTok1 : List Char -> Nat -> Nat -> Either LexErr (SnocList Token)

public export
lexTok2 : List Char -> Nat -> Nat -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok3 : List Char -> Nat -> Nat -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok4 : List Char -> Nat -> Nat -> SnocList Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok5 : List Char -> Nat -> Nat -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok6 : List Char -> Nat -> Nat -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok7 : List Char -> Nat -> Nat -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok8 : List Char -> Nat -> Nat -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok9 : List Char -> Nat -> Nat -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok10 : List Char -> Nat -> Nat -> SnocList Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok11 : List Char -> Nat -> Nat -> SnocList Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok12 : List Char -> Nat -> Nat -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok13 : List Char -> Nat -> Nat -> Integer -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok14 : List Char -> Nat -> Nat -> SnocList Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok15 : List Char -> Nat -> Nat -> SnocList Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok16 : List Char -> Nat -> Nat -> SnocList Char -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok17 : List Char -> Nat -> Nat -> Integer -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok18 : List Char -> Nat -> Nat -> SnocList String -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok19 : List Char -> Nat -> Nat -> SnocList String -> SnocList Token -> Either LexErr (SnocList Token)

public export
lexTok20 : List Char -> Nat -> Nat -> SnocList Char -> SnocList String -> SnocList Token -> Either LexErr (SnocList Token)

lexTok s = lexTok1 (unpack s) 0 0


lexTok1 str row col = lexTok2 str row col Lin
lexTok2 str@(c::cs) row col x0 =
  case c of
    '"' => lexTok4 cs row (S col) Lin x0
    '&' => lexTok5 cs row (S col) x0
    ',' => lexTok2 cs row (S col) ((:<) x0 Separator)
    '-' => lexTok6 cs row (S col) x0
    '.' => lexTok2 cs row (S col) ((:<) x0 Dot)
    '0' => lexTok2 cs row (S col) ((:<) x0 (IntegerLit 0))
    '<' => lexTok7 cs row (S col) x0
    '=' => lexTok8 cs row (S col) x0
    '>' => lexTok9 cs row (S col) x0
    _  => case isIdentStart c of
      True => lexTok10 cs row (S col) ((:<) Lin c) x0
      _  => case isLower c of
        True => lexTok11 cs row (S col) ((:<) Lin c) x0
        _  => case isSpace c of
          True => lexTok12 cs row (S col) x0
          _  => case (&&) ((<=) c '9') ((<=) '1' c) of
            True => lexTok13 cs row (S col) (toDigit c) x0
            _   => lexTok3 str row col x0
lexTok2 [] row col x0 = lexTok3 Nil row col x0

lexTok3 str@(c::cs) row col x0 = Left (Unexpected c)
lexTok3 [] row col x0 = Right x0

lexTok4 str@(c::cs) row col x1 x0 =
  case c of
    '\\' => lexTok15 cs row (S col) x1 x0
    _  => case validStrChar c of
      True => lexTok4 cs row (S col) ((:<) x1 c) x0
      _   => lexTok14 str row col x1 x0
lexTok4 [] row col x1 x0 = lexTok14 Nil row col x1 x0

lexTok5 str@(c::cs) row col x0 =
  case c of
    '&' => lexTok2 cs row (S col) ((:<) x0 AndOp)
    _   => Left (cast (Unexpected c))
lexTok5 [] row col x0 = Left (cast EOI)

lexTok6 str@(c::cs) row col x0 =
  case c of
    '-' => lexTok16 cs row (S col) Lin x0
    '0' => lexTok2 cs row (S col) ((:<) x0 (IntegerLit (negate 0)))
    _  => case (&&) ((<=) c '9') ((<=) '1' c) of
      True => lexTok17 cs row (S col) (toDigit c) x0
      _   => Left (cast (Unexpected c))
lexTok6 [] row col x0 = Left (cast EOI)

lexTok7 str@(c::cs) row col x0 =
  case c of
    '=' => lexTok2 cs row (S col) ((:<) x0 LTE)
    _   => lexTok2 str row col ((:<) x0 LT)
lexTok7 [] row col x0 = lexTok2 Nil row col ((:<) x0 LT)

lexTok8 str@(c::cs) row col x0 =
  case c of
    '=' => lexTok2 cs row (S col) ((:<) x0 EqOp)
    _   => lexTok2 str row col ((:<) x0 Equals)
lexTok8 [] row col x0 = lexTok2 Nil row col ((:<) x0 Equals)

lexTok9 str@(c::cs) row col x0 =
  case c of
    '=' => lexTok2 cs row (S col) ((:<) x0 GTE)
    _   => lexTok2 str row col ((:<) x0 GT)
lexTok9 [] row col x0 = lexTok2 Nil row col ((:<) x0 GT)

lexTok10 str@(c::cs) row col x1 x0 =
  case isIdentTrailing c of
    True => lexTok10 cs row (S col) ((:<) x1 c) x0
    _    => lexTok18 str row col ((:<) Lin (pack ((<>>) x1 Nil))) x0
lexTok10 [] row col x1 x0 = lexTok18 Nil row col ((:<) Lin (pack ((<>>) x1 Nil))) x0

lexTok11 str@(c::cs) row col x1 x0 =
  case isIdentTrailing c of
    True => lexTok11 cs row (S col) ((:<) x1 c) x0
    _    => lexTok2 str row col ((:<) x0 (PkgName (pack ((<>>) x1 Nil))))
lexTok11 [] row col x1 x0 = lexTok2 Nil row col ((:<) x0 (PkgName (pack ((<>>) x1 Nil))))

lexTok12 str@(c::cs) row col x0 =
  case isSpace c of
    True => lexTok12 cs row (S col) x0
    _    => lexTok2 str row col ((:<) x0 Space)
lexTok12 [] row col x0 = lexTok2 Nil row col ((:<) x0 Space)

lexTok13 str@(c::cs) row col x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexTok13 cs row (S col) ((+) ((*) x1 10) (toDigit c)) x0
    _    => lexTok2 str row col ((:<) x0 (IntegerLit x1))
lexTok13 [] row col x1 x0 = lexTok2 Nil row col ((:<) x0 (IntegerLit x1))

lexTok14 str@(c::cs) row col x1 x0 =
  case c of
    '"' => lexTok2 cs row (S col) ((:<) x0 (StringLit (pack ((<>>) x1 Nil))))
    _   => Left (cast (Unexpected c))
lexTok14 [] row col x1 x0 = Left (cast EOI)

lexTok15 str@(c::cs) row col x1 x0 =
  case (/=) c (fromChar '\n') of
    True => lexTok4 cs row (S col) ((:<) x1 c) x0
    _    => Left (cast (Unexpected c))
lexTok15 [] row col x1 x0 = Left (cast EOI)

lexTok16 str@(c::cs) row col x1 x0 =
  case (/=) c (fromChar '\n') of
    True => lexTok16 cs row (S col) ((:<) x1 c) x0
    _    => lexTok2 str row col ((:<) x0 (comment x1))
lexTok16 [] row col x1 x0 = lexTok2 Nil row col ((:<) x0 (comment x1))

lexTok17 str@(c::cs) row col x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexTok17 cs row (S col) ((+) ((*) x1 10) (toDigit c)) x0
    _    => lexTok2 str row col ((:<) x0 (IntegerLit (negate x1)))
lexTok17 [] row col x1 x0 = lexTok2 Nil row col ((:<) x0 (IntegerLit (negate x1)))

lexTok18 str@(c::cs) row col x1 x0 =
  case c of
    '.' => lexTok19 cs row (S col) x1 x0
    _   => lexTok2 str row col ((:<) x0 (module' x1))
lexTok18 [] row col x1 x0 = lexTok2 Nil row col ((:<) x0 (module' x1))

lexTok19 str@(c::cs) row col x1 x0 =
  case isIdentStart c of
    True => lexTok20 cs row (S col) ((:<) Lin c) x1 x0
    _    => Left (cast (Unexpected c))
lexTok19 [] row col x1 x0 = Left (cast EOI)

lexTok20 str@(c::cs) row col x2 x1 x0 =
  case isIdentTrailing c of
    True => lexTok20 cs row (S col) ((:<) x2 c) x1 x0
    _    => lexTok18 str row col ((:<) x1 (pack ((<>>) x2 Nil))) x0
lexTok20 [] row col x2 x1 x0 = lexTok18 Nil row col ((:<) x1 (pack ((<>>) x2 Nil))) x0



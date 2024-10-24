module Lexer

import Text.ILex.Util

%default total

public export
lexNat : String -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat1 : List Char -> Nat -> Nat -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat2 : List Char -> Nat -> Nat -> Pos -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat3 : List Char -> Nat -> Nat -> Pos -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat4 : List Char -> Nat -> Nat -> Integer -> Pos -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat5 : List Char -> Nat -> Nat -> SnocList (WBounds Integer) -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat6 : List Char -> Nat -> Nat -> Pos -> SnocList (WBounds Integer) -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat7 : List Char -> Nat -> Nat -> Pos -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat8 : List Char -> Nat -> Nat -> Pos -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat9 : List Char -> Nat -> Nat -> Pos -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat10 : List Char -> Nat -> Nat -> Pos -> SnocList (WBounds Integer) -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat11 : List Char -> Nat -> Nat -> Integer -> Pos -> SnocList (WBounds Integer) -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat12 : List Char -> Nat -> Nat -> SnocList (WBounds Integer) -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat13 : List Char -> Nat -> Nat -> Pos -> SnocList (WBounds Integer) -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat14 : List Char -> Nat -> Nat -> Pos -> SnocList (WBounds Integer) -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat15 : List Char -> Nat -> Nat -> Pos -> SnocList (WBounds Integer) -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat16 : List Char -> Nat -> Nat -> Integer -> Pos -> SnocList (WBounds Integer) -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat17 : List Char -> Nat -> Nat -> Integer -> Pos -> SnocList (WBounds Integer) -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat18 : List Char -> Nat -> Nat -> Integer -> Pos -> SnocList (WBounds Integer) -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat19 : List Char -> Nat -> Nat -> Integer -> Pos -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat20 : List Char -> Nat -> Nat -> Integer -> Pos -> Either LexErr (SnocList (WBounds Integer))

public export
lexNat21 : List Char -> Nat -> Nat -> Integer -> Pos -> Either LexErr (SnocList (WBounds Integer))

lexNat s = lexNat1 (unpack s) 0 0


lexNat1 str row col = lexNat2 str row col (P row col)
lexNat2 str@(c::cs) row col x0 =
  case c of
    '0' => lexNat3 cs row (S col) x0
    _  => case (&&) ((<=) c '9') ((<=) '1' c) of
      True => lexNat4 cs row (S col) (toDigit c) x0
      _   => Left (cast (Unexpected c))
lexNat2 [] row col x0 = Left (cast EOI)

lexNat3 str@(c::cs) row col x0 =
  case c of
    ',' => lexNat6 cs row (S col) (P row col) ((:<) Lin (WB x0 0 (P row col)))
    'b' => lexNat7 cs row (S col) x0
    'o' => lexNat8 cs row (S col) x0
    'x' => lexNat9 cs row (S col) x0
    _   => lexNat5 str row col ((:<) Lin (WB x0 0 (P row col)))
lexNat3 [] row col x0 = lexNat5 Nil row col ((:<) Lin (WB x0 0 (P row col)))

lexNat4 str@(c::cs) row col x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat4 cs row (S col) ((+) ((*) x1 10) (toDigit c)) x0
    _    => lexNat12 str row col ((:<) Lin (WB x0 x1 (P row col)))
lexNat4 [] row col x1 x0 = lexNat12 Nil row col ((:<) Lin (WB x0 x1 (P row col)))

lexNat5 str@(c::cs) row col x0 = Left (Unexpected c)
lexNat5 [] row col x0 = Right x0

lexNat6 str@(c::cs) row col x1 x0 =
  case c of
    '0' => lexNat10 cs row (S col) x1 x0
    _  => case (&&) ((<=) c '9') ((<=) '1' c) of
      True => lexNat11 cs row (S col) (toDigit c) x1 x0
      _   => Left (cast (Unexpected c))
lexNat6 [] row col x1 x0 = Left (cast EOI)

lexNat7 str@(c::cs) row col x0 =
  case (&&) ((<=) c '1') ((<=) '0' c) of
    True => lexNat19 cs row (S col) (toDigit c) x0
    _    => Left (cast (Unexpected c))
lexNat7 [] row col x0 = Left (cast EOI)

lexNat8 str@(c::cs) row col x0 =
  case (&&) ((<=) c '7') ((<=) '0' c) of
    True => lexNat20 cs row (S col) (toDigit c) x0
    _    => Left (cast (Unexpected c))
lexNat8 [] row col x0 = Left (cast EOI)

lexNat9 str@(c::cs) row col x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat21 cs row (S col) (toDigit c) x0
    _    =>
      case (&&) ((<=) c 'F') ((<=) 'A' c) of
        True => lexNat21 cs row (S col) (toHex (toLower c)) x0
        _    =>
          case (&&) ((<=) c 'f') ((<=) 'a' c) of
            True => lexNat21 cs row (S col) (toHex c) x0
            _    => Left (cast (Unexpected c))
lexNat9 [] row col x0 = Left (cast EOI)

lexNat10 str@(c::cs) row col x1 x0 =
  case c of
    'b' => lexNat13 cs row (S col) x1 x0
    'o' => lexNat14 cs row (S col) x1 x0
    'x' => lexNat15 cs row (S col) x1 x0
    _   => lexNat12 str row col ((:<) x0 (WB x1 0 (P row col)))
lexNat10 [] row col x1 x0 = lexNat12 Nil row col ((:<) x0 (WB x1 0 (P row col)))

lexNat11 str@(c::cs) row col x2 x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat11 cs row (S col) ((+) ((*) x2 10) (toDigit c)) x1 x0
    _    => lexNat12 str row col ((:<) x0 (WB x1 x2 (P row col)))
lexNat11 [] row col x2 x1 x0 = lexNat12 Nil row col ((:<) x0 (WB x1 x2 (P row col)))

lexNat12 str@(c::cs) row col x0 =
  case c of
    ',' => lexNat6 cs row (S col) (P row col) x0
    _   => lexNat5 str row col x0
lexNat12 [] row col x0 = lexNat5 Nil row col x0

lexNat13 str@(c::cs) row col x1 x0 =
  case (&&) ((<=) c '1') ((<=) '0' c) of
    True => lexNat16 cs row (S col) (toDigit c) x1 x0
    _    => Left (cast (Unexpected c))
lexNat13 [] row col x1 x0 = Left (cast EOI)

lexNat14 str@(c::cs) row col x1 x0 =
  case (&&) ((<=) c '7') ((<=) '0' c) of
    True => lexNat17 cs row (S col) (toDigit c) x1 x0
    _    => Left (cast (Unexpected c))
lexNat14 [] row col x1 x0 = Left (cast EOI)

lexNat15 str@(c::cs) row col x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat18 cs row (S col) (toDigit c) x1 x0
    _    =>
      case (&&) ((<=) c 'F') ((<=) 'A' c) of
        True => lexNat18 cs row (S col) (toHex (toLower c)) x1 x0
        _    =>
          case (&&) ((<=) c 'f') ((<=) 'a' c) of
            True => lexNat18 cs row (S col) (toHex c) x1 x0
            _    => Left (cast (Unexpected c))
lexNat15 [] row col x1 x0 = Left (cast EOI)

lexNat16 str@(c::cs) row col x2 x1 x0 =
  case (&&) ((<=) c '1') ((<=) '0' c) of
    True => lexNat16 cs row (S col) ((+) ((*) x2 2) (toDigit c)) x1 x0
    _    => lexNat12 str row col ((:<) x0 (WB x1 x2 (P row col)))
lexNat16 [] row col x2 x1 x0 = lexNat12 Nil row col ((:<) x0 (WB x1 x2 (P row col)))

lexNat17 str@(c::cs) row col x2 x1 x0 =
  case (&&) ((<=) c '7') ((<=) '0' c) of
    True => lexNat17 cs row (S col) ((+) ((*) x2 8) (toDigit c)) x1 x0
    _    => lexNat12 str row col ((:<) x0 (WB x1 x2 (P row col)))
lexNat17 [] row col x2 x1 x0 = lexNat12 Nil row col ((:<) x0 (WB x1 x2 (P row col)))

lexNat18 str@(c::cs) row col x2 x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat18 cs row (S col) ((+) ((*) x2 16) (toDigit c)) x1 x0
    _    =>
      case (&&) ((<=) c 'F') ((<=) 'A' c) of
        True => lexNat18 cs row (S col) ((+) ((*) x2 16) (toHex (toLower c))) x1 x0
        _    =>
          case (&&) ((<=) c 'f') ((<=) 'a' c) of
            True => lexNat18 cs row (S col) ((+) ((*) x2 16) (toHex c)) x1 x0
            _    => lexNat12 str row col ((:<) x0 (WB x1 x2 (P row col)))
lexNat18 [] row col x2 x1 x0 = lexNat12 Nil row col ((:<) x0 (WB x1 x2 (P row col)))

lexNat19 str@(c::cs) row col x1 x0 =
  case (&&) ((<=) c '1') ((<=) '0' c) of
    True => lexNat19 cs row (S col) ((+) ((*) x1 2) (toDigit c)) x0
    _    => lexNat12 str row col ((:<) Lin (WB x0 x1 (P row col)))
lexNat19 [] row col x1 x0 = lexNat12 Nil row col ((:<) Lin (WB x0 x1 (P row col)))

lexNat20 str@(c::cs) row col x1 x0 =
  case (&&) ((<=) c '7') ((<=) '0' c) of
    True => lexNat20 cs row (S col) ((+) ((*) x1 8) (toDigit c)) x0
    _    => lexNat12 str row col ((:<) Lin (WB x0 x1 (P row col)))
lexNat20 [] row col x1 x0 = lexNat12 Nil row col ((:<) Lin (WB x0 x1 (P row col)))

lexNat21 str@(c::cs) row col x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexNat21 cs row (S col) ((+) ((*) x1 16) (toDigit c)) x0
    _    =>
      case (&&) ((<=) c 'F') ((<=) 'A' c) of
        True => lexNat21 cs row (S col) ((+) ((*) x1 16) (toHex (toLower c))) x0
        _    =>
          case (&&) ((<=) c 'f') ((<=) 'a' c) of
            True => lexNat21 cs row (S col) ((+) ((*) x1 16) (toHex c)) x0
            _    => lexNat12 str row col ((:<) Lin (WB x0 x1 (P row col)))
lexNat21 [] row col x1 x0 = lexNat12 Nil row col ((:<) Lin (WB x0 x1 (P row col)))



module SmilesLexer

import Smiles
import Text.ILex.Util
import Text.Smiles
import Text.Smiles.Lexer

%hide Text.Smiles.Lexer.LexErr
%hide Data.List.Suffix.Result0.Unexpected
%hide Data.List.Suffix.Result0.EOI
%hide Text.ParseError.EOI

public export
smiles : String -> Either LexErr (SnocList SmilesToken)

public export
smiles1 : List Char -> Nat -> Nat -> Either LexErr (SnocList SmilesToken)

public export
smiles2 : List Char -> Nat -> Nat -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles3 : List Char -> Nat -> Nat -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles4 : List Char -> Nat -> Nat -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles5 : List Char -> Nat -> Nat -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles6 : List Char -> Nat -> Nat -> SnocList Ring -> SmilesAtom -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles7 : List Char -> Nat -> Nat -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles8 : List Char -> Nat -> Nat -> SnocList Ring -> SmilesAtom -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles9 : List Char -> Nat -> Nat -> RingNr -> SnocList Ring -> SmilesAtom -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles10 : List Char -> Nat -> Nat -> Integer -> SnocList Ring -> SmilesAtom -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles11 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles12 : List Char -> Nat -> Nat -> Integer -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles13 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles14 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles15 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles16 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles17 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles18 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles19 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles20 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles21 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles22 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles23 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles24 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles25 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles26 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles27 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles28 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles29 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles30 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles31 : List Char -> Nat -> Nat -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles32 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles33 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles34 : List Char -> Nat -> Nat -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles35 : List Char -> Nat -> Nat -> AromIsotope -> Chirality -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles36 : List Char -> Nat -> Nat -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles37 : List Char -> Nat -> Nat -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles38 : List Char -> Nat -> Nat -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles39 : List Char -> Nat -> Nat -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles40 : List Char -> Nat -> Nat -> AromIsotope -> Chirality -> HCount -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles41 : List Char -> Nat -> Nat -> AromIsotope -> Chirality -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles42 : List Char -> Nat -> Nat -> SmilesAtom -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles43 : List Char -> Nat -> Nat -> AromIsotope -> Chirality -> HCount -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles44 : List Char -> Nat -> Nat -> AromIsotope -> Chirality -> HCount -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles45 : List Char -> Nat -> Nat -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles46 : List Char -> Nat -> Nat -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles47 : List Char -> Nat -> Nat -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

smiles s = smiles1 (unpack s) 0 0


smiles1 str row col = smiles2 str row col Lin
smiles2 str@(c::cs) row col x0 =
  case c of
    '#' => smiles2 cs row (S col) ((:<) x0 (TB Trpl))
    '$' => smiles2 cs row (S col) ((:<) x0 (TB Quad))
    '(' => smiles2 cs row (S col) ((:<) x0 PO)
    ')' => smiles2 cs row (S col) ((:<) x0 PC)
    '-' => smiles2 cs row (S col) ((:<) x0 (TB Sngl))
    '.' => smiles2 cs row (S col) ((:<) x0 Dot)
    '/' => smiles2 cs row (S col) ((:<) x0 (TB FW))
    ':' => smiles2 cs row (S col) ((:<) x0 (TB Arom))
    '=' => smiles2 cs row (S col) ((:<) x0 (TB Dbl))
    'B' => smiles4 cs row (S col) x0
    'C' => smiles5 cs row (S col) x0
    'F' => smiles6 cs row (S col) Lin (SubsetAtom F False) x0
    'I' => smiles6 cs row (S col) Lin (SubsetAtom I False) x0
    'N' => smiles6 cs row (S col) Lin (SubsetAtom N False) x0
    'O' => smiles6 cs row (S col) Lin (SubsetAtom O False) x0
    'P' => smiles6 cs row (S col) Lin (SubsetAtom P False) x0
    'S' => smiles6 cs row (S col) Lin (SubsetAtom S False) x0
    '[' => smiles7 cs row (S col) x0
    '\\' => smiles2 cs row (S col) ((:<) x0 (TB BW))
    'b' => smiles6 cs row (S col) Lin (SubsetAtom B True) x0
    'c' => smiles6 cs row (S col) Lin (SubsetAtom C True) x0
    'n' => smiles6 cs row (S col) Lin (SubsetAtom N True) x0
    'o' => smiles6 cs row (S col) Lin (SubsetAtom O True) x0
    'p' => smiles6 cs row (S col) Lin (SubsetAtom P True) x0
    's' => smiles6 cs row (S col) Lin (SubsetAtom S True) x0
    _   => smiles3 str row col x0
smiles2 [] row col x0 = smiles3 Nil row col x0

smiles3 str@(c::cs) row col x0 = Left (Unexpected c)
smiles3 [] row col x0 = Right x0

smiles4 str@(c::cs) row col x0 =
  case c of
    '%' => smiles8 cs row (S col) Lin (SubsetAtom B False) x0
    'r' => smiles6 cs row (S col) Lin (SubsetAtom Br False) x0
    _  => case (&&) ((<=) c '9') ((<=) '0' c) of
      True => smiles9 cs row (S col) (toRingNr (toDigit c)) Lin (SubsetAtom B False) x0
      _   => smiles2 str row col ((:<) x0 (TA (SubsetAtom B False) Lin))
smiles4 [] row col x0 = smiles2 Nil row col ((:<) x0 (TA (SubsetAtom B False) Lin))

smiles5 str@(c::cs) row col x0 =
  case c of
    '%' => smiles8 cs row (S col) Lin (SubsetAtom C False) x0
    'l' => smiles6 cs row (S col) Lin (SubsetAtom Cl False) x0
    _  => case (&&) ((<=) c '9') ((<=) '0' c) of
      True => smiles9 cs row (S col) (toRingNr (toDigit c)) Lin (SubsetAtom C False) x0
      _   => smiles2 str row col ((:<) x0 (TA (SubsetAtom C False) Lin))
smiles5 [] row col x0 = smiles2 Nil row col ((:<) x0 (TA (SubsetAtom C False) Lin))

smiles6 str@(c::cs) row col x2 x1 x0 =
  case c of
    '%' => smiles8 cs row (S col) x2 x1 x0
    _  => case (&&) ((<=) c '9') ((<=) '0' c) of
      True => smiles9 cs row (S col) (toRingNr (toDigit c)) x2 x1 x0
      _   => smiles2 str row col ((:<) x0 (TA x1 x2))
smiles6 [] row col x2 x1 x0 = smiles2 Nil row col ((:<) x0 (TA x1 x2))

smiles7 str@(c::cs) row col x0 =
  case c of
    '0' => smiles11 cs row (S col) (refineMassNr (cast 0)) x0
    _  => case (&&) ((<=) c '9') ((<=) '1' c) of
      True => smiles12 cs row (S col) (toDigit c) x0
      _   => smiles11 str row col Nothing x0
smiles7 [] row col x0 = smiles11 Nil row col Nothing x0

smiles8 str@(c::cs) row col x2 x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => smiles10 cs row (S col) (toDigit c) x2 x1 x0
    _    => Left (cast (Unexpected c))
smiles8 [] row col x2 x1 x0 = Left (cast EOI)

smiles9 str@(c::cs) row col x3 x2 x1 x0 =
  case c of
    '#' => smiles6 cs row (S col) ((:<) x2 (R x3 (Just Trpl))) x1 x0
    '$' => smiles6 cs row (S col) ((:<) x2 (R x3 (Just Quad))) x1 x0
    '-' => smiles6 cs row (S col) ((:<) x2 (R x3 (Just Sngl))) x1 x0
    '/' => smiles6 cs row (S col) ((:<) x2 (R x3 (Just FW))) x1 x0
    ':' => smiles6 cs row (S col) ((:<) x2 (R x3 (Just Arom))) x1 x0
    '=' => smiles6 cs row (S col) ((:<) x2 (R x3 (Just Dbl))) x1 x0
    '\\' => smiles6 cs row (S col) ((:<) x2 (R x3 (Just BW))) x1 x0
    _   => smiles6 str row col ((:<) x2 (R x3 Nothing)) x1 x0
smiles9 [] row col x3 x2 x1 x0 = smiles6 Nil row col ((:<) x2 (R x3 Nothing)) x1 x0

smiles10 str@(c::cs) row col x3 x2 x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => smiles9 cs row (S col) (toRingNr ((+) ((*) x3 10) (toDigit c))) x2 x1 x0
    _    => Left (cast (Unexpected c))
smiles10 [] row col x3 x2 x1 x0 = Left (cast EOI)

smiles11 str@(c::cs) row col x1 x0 =
  case c of
    'A' => smiles13 cs row (S col) x1 x0
    'B' => smiles14 cs row (S col) x1 x0
    'C' => smiles15 cs row (S col) x1 x0
    'D' => smiles16 cs row (S col) x1 x0
    'E' => smiles17 cs row (S col) x1 x0
    'F' => smiles18 cs row (S col) x1 x0
    'G' => smiles19 cs row (S col) x1 x0
    'H' => smiles20 cs row (S col) x1 x0
    'I' => smiles21 cs row (S col) x1 x0
    'K' => smiles22 cs row (S col) x1 x0
    'L' => smiles23 cs row (S col) x1 x0
    'M' => smiles24 cs row (S col) x1 x0
    'N' => smiles25 cs row (S col) x1 x0
    'O' => smiles26 cs row (S col) x1 x0
    'P' => smiles27 cs row (S col) x1 x0
    'R' => smiles28 cs row (S col) x1 x0
    'S' => smiles29 cs row (S col) x1 x0
    'T' => smiles30 cs row (S col) x1 x0
    'U' => smiles31 cs row (S col) (MkAI U x1 False) x0
    'V' => smiles31 cs row (S col) (MkAI V x1 False) x0
    'W' => smiles31 cs row (S col) (MkAI W x1 False) x0
    'X' => smiles32 cs row (S col) x1 x0
    'Y' => smiles33 cs row (S col) x1 x0
    'Z' => smiles34 cs row (S col) x1 x0
    _   => Left (cast (Unexpected c))
smiles11 [] row col x1 x0 = Left (cast EOI)

smiles12 str@(c::cs) row col x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => smiles12 cs row (S col) ((+) ((*) x1 10) (toDigit c)) x0
    _    => smiles11 str row col (refineMassNr (cast x1)) x0
smiles12 [] row col x1 x0 = smiles11 Nil row col (refineMassNr (cast x1)) x0

smiles13 str@(c::cs) row col x1 x0 =
  case c of
    'c' => smiles31 cs row (S col) (MkAI Ac x1 False) x0
    'g' => smiles31 cs row (S col) (MkAI Ag x1 False) x0
    'l' => smiles31 cs row (S col) (MkAI Al x1 False) x0
    'm' => smiles31 cs row (S col) (MkAI Am x1 False) x0
    'r' => smiles31 cs row (S col) (MkAI Ar x1 False) x0
    's' => smiles31 cs row (S col) (MkAI As x1 False) x0
    't' => smiles31 cs row (S col) (MkAI At x1 False) x0
    'u' => smiles31 cs row (S col) (MkAI Au x1 False) x0
    _   => Left (cast (Unexpected c))
smiles13 [] row col x1 x0 = Left (cast EOI)

smiles14 str@(c::cs) row col x1 x0 =
  case c of
    '@' => smiles36 cs row (S col) (MkAI B x1 False) x0
    'A' => smiles37 cs row (S col) (MkAI B x1 False) x0
    'S' => smiles38 cs row (S col) (MkAI B x1 False) x0
    'T' => smiles39 cs row (S col) (MkAI B x1 False) x0
    'a' => smiles31 cs row (S col) (MkAI Ba x1 False) x0
    'e' => smiles31 cs row (S col) (MkAI Be x1 False) x0
    'h' => smiles31 cs row (S col) (MkAI Bh x1 False) x0
    'i' => smiles31 cs row (S col) (MkAI Bi x1 False) x0
    'k' => smiles31 cs row (S col) (MkAI Bk x1 False) x0
    'r' => smiles31 cs row (S col) (MkAI Br x1 False) x0
    _   => smiles35 str row col (MkAI B x1 False) None x0
smiles14 [] row col x1 x0 = smiles35 Nil row col (MkAI B x1 False) None x0

smiles15 str@(c::cs) row col x1 x0 =
  case c of
    '@' => smiles36 cs row (S col) (MkAI C x1 False) x0
    'A' => smiles37 cs row (S col) (MkAI C x1 False) x0
    'S' => smiles38 cs row (S col) (MkAI C x1 False) x0
    'T' => smiles39 cs row (S col) (MkAI C x1 False) x0
    'a' => smiles31 cs row (S col) (MkAI Ca x1 False) x0
    'd' => smiles31 cs row (S col) (MkAI Cd x1 False) x0
    'e' => smiles31 cs row (S col) (MkAI Ce x1 False) x0
    'f' => smiles31 cs row (S col) (MkAI Cf x1 False) x0
    'l' => smiles31 cs row (S col) (MkAI Cl x1 False) x0
    'm' => smiles31 cs row (S col) (MkAI Cm x1 False) x0
    'n' => smiles31 cs row (S col) (MkAI Cn x1 False) x0
    'o' => smiles31 cs row (S col) (MkAI Co x1 False) x0
    'r' => smiles31 cs row (S col) (MkAI Cr x1 False) x0
    's' => smiles31 cs row (S col) (MkAI Cs x1 False) x0
    'u' => smiles31 cs row (S col) (MkAI Cu x1 False) x0
    _   => smiles35 str row col (MkAI C x1 False) None x0
smiles15 [] row col x1 x0 = smiles35 Nil row col (MkAI C x1 False) None x0

smiles16 str@(c::cs) row col x1 x0 =
  case c of
    'b' => smiles31 cs row (S col) (MkAI Db x1 False) x0
    's' => smiles31 cs row (S col) (MkAI Ds x1 False) x0
    'y' => smiles31 cs row (S col) (MkAI Dy x1 False) x0
    _   => Left (cast (Unexpected c))
smiles16 [] row col x1 x0 = Left (cast EOI)

smiles17 str@(c::cs) row col x1 x0 =
  case c of
    'r' => smiles31 cs row (S col) (MkAI Er x1 False) x0
    's' => smiles31 cs row (S col) (MkAI Es x1 False) x0
    'u' => smiles31 cs row (S col) (MkAI Eu x1 False) x0
    _   => Left (cast (Unexpected c))
smiles17 [] row col x1 x0 = Left (cast EOI)

smiles18 str@(c::cs) row col x1 x0 =
  case c of
    '@' => smiles36 cs row (S col) (MkAI F x1 False) x0
    'A' => smiles37 cs row (S col) (MkAI F x1 False) x0
    'S' => smiles38 cs row (S col) (MkAI F x1 False) x0
    'T' => smiles39 cs row (S col) (MkAI F x1 False) x0
    'e' => smiles31 cs row (S col) (MkAI Fe x1 False) x0
    'l' => smiles31 cs row (S col) (MkAI Fl x1 False) x0
    'm' => smiles31 cs row (S col) (MkAI Fm x1 False) x0
    'r' => smiles31 cs row (S col) (MkAI Fr x1 False) x0
    _   => smiles35 str row col (MkAI F x1 False) None x0
smiles18 [] row col x1 x0 = smiles35 Nil row col (MkAI F x1 False) None x0

smiles19 str@(c::cs) row col x1 x0 =
  case c of
    'a' => smiles31 cs row (S col) (MkAI Ga x1 False) x0
    'd' => smiles31 cs row (S col) (MkAI Gd x1 False) x0
    'e' => smiles31 cs row (S col) (MkAI Ge x1 False) x0
    _   => Left (cast (Unexpected c))
smiles19 [] row col x1 x0 = Left (cast EOI)

smiles20 str@(c::cs) row col x1 x0 =
  case c of
    '@' => smiles36 cs row (S col) (MkAI H x1 False) x0
    'A' => smiles37 cs row (S col) (MkAI H x1 False) x0
    'S' => smiles38 cs row (S col) (MkAI H x1 False) x0
    'T' => smiles39 cs row (S col) (MkAI H x1 False) x0
    'e' => smiles31 cs row (S col) (MkAI He x1 False) x0
    'f' => smiles31 cs row (S col) (MkAI Hf x1 False) x0
    'g' => smiles31 cs row (S col) (MkAI Hg x1 False) x0
    'o' => smiles31 cs row (S col) (MkAI Ho x1 False) x0
    's' => smiles31 cs row (S col) (MkAI Hs x1 False) x0
    _   => smiles35 str row col (MkAI H x1 False) None x0
smiles20 [] row col x1 x0 = smiles35 Nil row col (MkAI H x1 False) None x0

smiles21 str@(c::cs) row col x1 x0 =
  case c of
    '@' => smiles36 cs row (S col) (MkAI I x1 False) x0
    'A' => smiles37 cs row (S col) (MkAI I x1 False) x0
    'S' => smiles38 cs row (S col) (MkAI I x1 False) x0
    'T' => smiles39 cs row (S col) (MkAI I x1 False) x0
    'n' => smiles31 cs row (S col) (MkAI In x1 False) x0
    'r' => smiles31 cs row (S col) (MkAI Ir x1 False) x0
    _   => smiles35 str row col (MkAI I x1 False) None x0
smiles21 [] row col x1 x0 = smiles35 Nil row col (MkAI I x1 False) None x0

smiles22 str@(c::cs) row col x1 x0 =
  case c of
    '@' => smiles36 cs row (S col) (MkAI K x1 False) x0
    'A' => smiles37 cs row (S col) (MkAI K x1 False) x0
    'S' => smiles38 cs row (S col) (MkAI K x1 False) x0
    'T' => smiles39 cs row (S col) (MkAI K x1 False) x0
    'r' => smiles31 cs row (S col) (MkAI Kr x1 False) x0
    _   => smiles35 str row col (MkAI K x1 False) None x0
smiles22 [] row col x1 x0 = smiles35 Nil row col (MkAI K x1 False) None x0

smiles23 str@(c::cs) row col x1 x0 =
  case c of
    'a' => smiles31 cs row (S col) (MkAI La x1 False) x0
    'i' => smiles31 cs row (S col) (MkAI Li x1 False) x0
    'r' => smiles31 cs row (S col) (MkAI Lr x1 False) x0
    'u' => smiles31 cs row (S col) (MkAI Lu x1 False) x0
    'v' => smiles31 cs row (S col) (MkAI Lv x1 False) x0
    _   => Left (cast (Unexpected c))
smiles23 [] row col x1 x0 = Left (cast EOI)

smiles24 str@(c::cs) row col x1 x0 =
  case c of
    'c' => smiles31 cs row (S col) (MkAI Mc x1 False) x0
    'd' => smiles31 cs row (S col) (MkAI Md x1 False) x0
    'g' => smiles31 cs row (S col) (MkAI Mg x1 False) x0
    'n' => smiles31 cs row (S col) (MkAI Mn x1 False) x0
    'o' => smiles31 cs row (S col) (MkAI Mo x1 False) x0
    't' => smiles31 cs row (S col) (MkAI Mt x1 False) x0
    _   => Left (cast (Unexpected c))
smiles24 [] row col x1 x0 = Left (cast EOI)

smiles25 str@(c::cs) row col x1 x0 =
  case c of
    '@' => smiles36 cs row (S col) (MkAI N x1 False) x0
    'A' => smiles37 cs row (S col) (MkAI N x1 False) x0
    'S' => smiles38 cs row (S col) (MkAI N x1 False) x0
    'T' => smiles39 cs row (S col) (MkAI N x1 False) x0
    'a' => smiles31 cs row (S col) (MkAI Na x1 False) x0
    'b' => smiles31 cs row (S col) (MkAI Nb x1 False) x0
    'd' => smiles31 cs row (S col) (MkAI Nd x1 False) x0
    'e' => smiles31 cs row (S col) (MkAI Ne x1 False) x0
    'h' => smiles31 cs row (S col) (MkAI Nh x1 False) x0
    'i' => smiles31 cs row (S col) (MkAI Ni x1 False) x0
    'o' => smiles31 cs row (S col) (MkAI No x1 False) x0
    'p' => smiles31 cs row (S col) (MkAI Np x1 False) x0
    _   => smiles35 str row col (MkAI N x1 False) None x0
smiles25 [] row col x1 x0 = smiles35 Nil row col (MkAI N x1 False) None x0

smiles26 str@(c::cs) row col x1 x0 =
  case c of
    '@' => smiles36 cs row (S col) (MkAI O x1 False) x0
    'A' => smiles37 cs row (S col) (MkAI O x1 False) x0
    'S' => smiles38 cs row (S col) (MkAI O x1 False) x0
    'T' => smiles39 cs row (S col) (MkAI O x1 False) x0
    'g' => smiles31 cs row (S col) (MkAI Og x1 False) x0
    's' => smiles31 cs row (S col) (MkAI Os x1 False) x0
    _   => smiles35 str row col (MkAI O x1 False) None x0
smiles26 [] row col x1 x0 = smiles35 Nil row col (MkAI O x1 False) None x0

smiles27 str@(c::cs) row col x1 x0 =
  case c of
    '@' => smiles36 cs row (S col) (MkAI P x1 False) x0
    'A' => smiles37 cs row (S col) (MkAI P x1 False) x0
    'S' => smiles38 cs row (S col) (MkAI P x1 False) x0
    'T' => smiles39 cs row (S col) (MkAI P x1 False) x0
    'a' => smiles31 cs row (S col) (MkAI Pa x1 False) x0
    'b' => smiles31 cs row (S col) (MkAI Pb x1 False) x0
    'd' => smiles31 cs row (S col) (MkAI Pd x1 False) x0
    'm' => smiles31 cs row (S col) (MkAI Pm x1 False) x0
    'o' => smiles31 cs row (S col) (MkAI Po x1 False) x0
    'r' => smiles31 cs row (S col) (MkAI Pr x1 False) x0
    't' => smiles31 cs row (S col) (MkAI Pt x1 False) x0
    'u' => smiles31 cs row (S col) (MkAI Pu x1 False) x0
    _   => smiles35 str row col (MkAI P x1 False) None x0
smiles27 [] row col x1 x0 = smiles35 Nil row col (MkAI P x1 False) None x0

smiles28 str@(c::cs) row col x1 x0 =
  case c of
    'a' => smiles31 cs row (S col) (MkAI Ra x1 False) x0
    'b' => smiles31 cs row (S col) (MkAI Rb x1 False) x0
    'e' => smiles31 cs row (S col) (MkAI Re x1 False) x0
    'f' => smiles31 cs row (S col) (MkAI Rf x1 False) x0
    'g' => smiles31 cs row (S col) (MkAI Rg x1 False) x0
    'h' => smiles31 cs row (S col) (MkAI Rh x1 False) x0
    'n' => smiles31 cs row (S col) (MkAI Rn x1 False) x0
    'u' => smiles31 cs row (S col) (MkAI Ru x1 False) x0
    _   => Left (cast (Unexpected c))
smiles28 [] row col x1 x0 = Left (cast EOI)

smiles29 str@(c::cs) row col x1 x0 =
  case c of
    '@' => smiles36 cs row (S col) (MkAI S x1 False) x0
    'A' => smiles37 cs row (S col) (MkAI S x1 False) x0
    'S' => smiles38 cs row (S col) (MkAI S x1 False) x0
    'T' => smiles39 cs row (S col) (MkAI S x1 False) x0
    'b' => smiles31 cs row (S col) (MkAI Sb x1 False) x0
    'c' => smiles31 cs row (S col) (MkAI Sc x1 False) x0
    'e' => smiles31 cs row (S col) (MkAI Se x1 False) x0
    'g' => smiles31 cs row (S col) (MkAI Sg x1 False) x0
    'i' => smiles31 cs row (S col) (MkAI Si x1 False) x0
    'm' => smiles31 cs row (S col) (MkAI Sm x1 False) x0
    'n' => smiles31 cs row (S col) (MkAI Sn x1 False) x0
    'r' => smiles31 cs row (S col) (MkAI Sr x1 False) x0
    _   => smiles35 str row col (MkAI S x1 False) None x0
smiles29 [] row col x1 x0 = smiles35 Nil row col (MkAI S x1 False) None x0

smiles30 str@(c::cs) row col x1 x0 =
  case c of
    'a' => smiles31 cs row (S col) (MkAI Ta x1 False) x0
    'b' => smiles31 cs row (S col) (MkAI Tb x1 False) x0
    'c' => smiles31 cs row (S col) (MkAI Tc x1 False) x0
    'e' => smiles31 cs row (S col) (MkAI Te x1 False) x0
    'h' => smiles31 cs row (S col) (MkAI Th x1 False) x0
    'i' => smiles31 cs row (S col) (MkAI Ti x1 False) x0
    'l' => smiles31 cs row (S col) (MkAI Tl x1 False) x0
    'm' => smiles31 cs row (S col) (MkAI Tm x1 False) x0
    's' => smiles31 cs row (S col) (MkAI Ts x1 False) x0
    _   => Left (cast (Unexpected c))
smiles30 [] row col x1 x0 = Left (cast EOI)

smiles31 str@(c::cs) row col x1 x0 =
  case c of
    '@' => smiles36 cs row (S col) x1 x0
    'A' => smiles37 cs row (S col) x1 x0
    'S' => smiles38 cs row (S col) x1 x0
    'T' => smiles39 cs row (S col) x1 x0
    _   => smiles35 str row col x1 None x0
smiles31 [] row col x1 x0 = smiles35 Nil row col x1 None x0

smiles32 str@(c::cs) row col x1 x0 =
  case c of
    'e' => smiles31 cs row (S col) (MkAI Xe x1 False) x0
    _   => Left (cast (Unexpected c))
smiles32 [] row col x1 x0 = Left (cast EOI)

smiles33 str@(c::cs) row col x1 x0 =
  case c of
    '@' => smiles36 cs row (S col) (MkAI Y x1 False) x0
    'A' => smiles37 cs row (S col) (MkAI Y x1 False) x0
    'S' => smiles38 cs row (S col) (MkAI Y x1 False) x0
    'T' => smiles39 cs row (S col) (MkAI Y x1 False) x0
    'b' => smiles31 cs row (S col) (MkAI Yb x1 False) x0
    _   => smiles35 str row col (MkAI Y x1 False) None x0
smiles33 [] row col x1 x0 = smiles35 Nil row col (MkAI Y x1 False) None x0

smiles34 str@(c::cs) row col x1 x0 =
  case c of
    'n' => smiles31 cs row (S col) (MkAI Zn x1 False) x0
    'r' => smiles31 cs row (S col) (MkAI Zr x1 False) x0
    _   => Left (cast (Unexpected c))
smiles34 [] row col x1 x0 = Left (cast EOI)

smiles35 str@(c::cs) row col x2 x1 x0 =
  case c of
    'H' => smiles41 cs row (S col) x2 x1 x0
    _   => smiles40 str row col x2 x1 (MkHCount (fromInteger 0)) x0
smiles35 [] row col x2 x1 x0 = smiles40 Nil row col x2 x1 (MkHCount (fromInteger 0)) x0

smiles36 str@(c::cs) row col x1 x0 =
  case c of
    '@' => smiles35 cs row (S col) x1 CCW x0
    'H' => smiles41 cs row (S col) x1 CW x0
    _   => smiles40 str row col x1 CW (MkHCount (fromInteger 0)) x0
smiles36 [] row col x1 x0 = smiles40 Nil row col x1 CW (MkHCount (fromInteger 0)) x0

smiles37 str@(c::cs) row col x1 x0 =
  case c of
    'L' => smiles45 cs row (S col) x1 x0
    _   => Left (cast (Unexpected c))
smiles37 [] row col x1 x0 = Left (cast EOI)

smiles38 str@(c::cs) row col x1 x0 =
  case c of
    'P' => smiles46 cs row (S col) x1 x0
    _   => Left (cast (Unexpected c))
smiles38 [] row col x1 x0 = Left (cast EOI)

smiles39 str@(c::cs) row col x1 x0 =
  case c of
    'H' => smiles47 cs row (S col) x1 x0
    _   => Left (cast (Unexpected c))
smiles39 [] row col x1 x0 = Left (cast EOI)

smiles40 str@(c::cs) row col x3 x2 x1 x0 =
  case c of
    '+' => smiles43 cs row (S col) x3 x2 x1 x0
    '-' => smiles44 cs row (S col) x3 x2 x1 x0
    _   => smiles42 str row col (bracket x3 x2 x1 (MkCharge (fromInteger 0))) x0
smiles40 [] row col x3 x2 x1 x0 = smiles42 Nil row col (bracket x3 x2 x1 (MkCharge (fromInteger 0))) x0

smiles41 str@(c::cs) row col x2 x1 x0 =
  case c of
    '+' => smiles43 cs row (S col) x2 x1 (MkHCount (fromInteger 1)) x0
    '-' => smiles44 cs row (S col) x2 x1 (MkHCount (fromInteger 1)) x0
    _  => case (&&) ((<=) c '9') ((<=) '1' c) of
      True => smiles40 cs row (S col) x2 x1 (fromMaybe (fromInteger 0) (refineHCount (cast (toDigit c)))) x0
      _   => smiles42 str row col (bracket x2 x1 (MkHCount (fromInteger 1)) (MkCharge (fromInteger 0))) x0
smiles41 [] row col x2 x1 x0 = smiles42 Nil row col (bracket x2 x1 (MkHCount (fromInteger 1)) (MkCharge (fromInteger 0))) x0

smiles42 str@(c::cs) row col x1 x0 =
  case c of
    ']' => smiles6 cs row (S col) Lin x1 x0
    _   => Left (cast (Unexpected c))
smiles42 [] row col x1 x0 = Left (cast EOI)

smiles43 str@(c::cs) row col x3 x2 x1 x0 =
  case c of
    '+' => smiles42 cs row (S col) (bracket x3 x2 x1 (MkCharge (fromInteger 2))) x0
    ']' => smiles6 cs row (S col) Lin (bracket x3 x2 x1 (MkCharge (fromInteger 1))) x0
    _   => Left (cast (Unexpected c))
smiles43 [] row col x3 x2 x1 x0 = Left (cast EOI)

smiles44 str@(c::cs) row col x3 x2 x1 x0 =
  case c of
    '-' => smiles42 cs row (S col) (bracket x3 x2 x1 (MkCharge (fromInteger (-2)))) x0
    ']' => smiles6 cs row (S col) Lin (bracket x3 x2 x1 (MkCharge (fromInteger (-1)))) x0
    _   => Left (cast (Unexpected c))
smiles44 [] row col x3 x2 x1 x0 = Left (cast EOI)

smiles45 str@(c::cs) row col x1 x0 =
  case c of
    '1' => smiles35 cs row (S col) x1 AL1 x0
    '2' => smiles35 cs row (S col) x1 AL2 x0
    _   => Left (cast (Unexpected c))
smiles45 [] row col x1 x0 = Left (cast EOI)

smiles46 str@(c::cs) row col x1 x0 =
  case c of
    '1' => smiles35 cs row (S col) x1 SP1 x0
    '2' => smiles35 cs row (S col) x1 SP2 x0
    '3' => smiles35 cs row (S col) x1 SP3 x0
    _   => Left (cast (Unexpected c))
smiles46 [] row col x1 x0 = Left (cast EOI)

smiles47 str@(c::cs) row col x1 x0 =
  case c of
    '1' => smiles35 cs row (S col) x1 TH1 x0
    '2' => smiles35 cs row (S col) x1 TH2 x0
    _   => Left (cast (Unexpected c))
smiles47 [] row col x1 x0 = Left (cast EOI)



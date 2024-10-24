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
smiles1 : List Char -> Either LexErr (SnocList SmilesToken)

public export
smiles2 : List Char -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles3 : List Char -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles4 : List Char -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles5 : List Char -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles6 : List Char -> SnocList Ring -> SmilesAtom -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles7 : List Char -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles8 : List Char -> SnocList Ring -> SmilesAtom -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles9 : List Char -> RingNr -> SnocList Ring -> SmilesAtom -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles10 : List Char -> Integer -> SnocList Ring -> SmilesAtom -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles11 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles12 : List Char -> Integer -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles13 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles14 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles15 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles16 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles17 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles18 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles19 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles20 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles21 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles22 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles23 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles24 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles25 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles26 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles27 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles28 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles29 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles30 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles31 : List Char -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles32 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles33 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles34 : List Char -> Maybe MassNr -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles35 : List Char -> AromIsotope -> Chirality -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles36 : List Char -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles37 : List Char -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles38 : List Char -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles39 : List Char -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles40 : List Char -> AromIsotope -> Chirality -> HCount -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles41 : List Char -> AromIsotope -> Chirality -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles42 : List Char -> SmilesAtom -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles43 : List Char -> AromIsotope -> Chirality -> HCount -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles44 : List Char -> AromIsotope -> Chirality -> HCount -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles45 : List Char -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles46 : List Char -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

public export
smiles47 : List Char -> AromIsotope -> SnocList SmilesToken -> Either LexErr (SnocList SmilesToken)

smiles = smiles1 . unpack

smiles1 str = smiles2 str Lin
smiles2 str@(c::cs) x0 =
  case c of
    '#' => smiles2 cs ((:<) x0 (TB Trpl))
    '$' => smiles2 cs ((:<) x0 (TB Quad))
    '(' => smiles2 cs ((:<) x0 PO)
    ')' => smiles2 cs ((:<) x0 PC)
    '-' => smiles2 cs ((:<) x0 (TB Sngl))
    '.' => smiles2 cs ((:<) x0 Dot)
    '/' => smiles2 cs ((:<) x0 (TB FW))
    ':' => smiles2 cs ((:<) x0 (TB Arom))
    '=' => smiles2 cs ((:<) x0 (TB Dbl))
    'B' => smiles4 cs x0
    'C' => smiles5 cs x0
    'F' => smiles6 cs Lin (SubsetAtom F False) x0
    'I' => smiles6 cs Lin (SubsetAtom I False) x0
    'N' => smiles6 cs Lin (SubsetAtom N False) x0
    'O' => smiles6 cs Lin (SubsetAtom O False) x0
    'P' => smiles6 cs Lin (SubsetAtom P False) x0
    'S' => smiles6 cs Lin (SubsetAtom S False) x0
    '[' => smiles7 cs x0
    '\\' => smiles2 cs ((:<) x0 (TB BW))
    'b' => smiles6 cs Lin (SubsetAtom B True) x0
    'c' => smiles6 cs Lin (SubsetAtom C True) x0
    'n' => smiles6 cs Lin (SubsetAtom N True) x0
    'o' => smiles6 cs Lin (SubsetAtom O True) x0
    'p' => smiles6 cs Lin (SubsetAtom P True) x0
    's' => smiles6 cs Lin (SubsetAtom S True) x0
    _   => smiles3 str x0
smiles2 [] x0 = smiles3 Nil x0

smiles3 str@(c::cs) x0 = Left (Unexpected c)
smiles3 [] x0 = Right x0

smiles4 str@(c::cs) x0 =
  case c of
    '%' => smiles8 cs Lin (SubsetAtom B False) x0
    'r' => smiles6 cs Lin (SubsetAtom Br False) x0
    _  => case (&&) ((<=) c '9') ((<=) '0' c) of
      True => smiles9 cs (toRingNr (toDigit c)) Lin (SubsetAtom B False) x0
      _   => smiles2 str ((:<) x0 (TA (SubsetAtom B False) Lin))
smiles4 [] x0 = smiles2 Nil ((:<) x0 (TA (SubsetAtom B False) Lin))

smiles5 str@(c::cs) x0 =
  case c of
    '%' => smiles8 cs Lin (SubsetAtom C False) x0
    'l' => smiles6 cs Lin (SubsetAtom Cl False) x0
    _  => case (&&) ((<=) c '9') ((<=) '0' c) of
      True => smiles9 cs (toRingNr (toDigit c)) Lin (SubsetAtom C False) x0
      _   => smiles2 str ((:<) x0 (TA (SubsetAtom C False) Lin))
smiles5 [] x0 = smiles2 Nil ((:<) x0 (TA (SubsetAtom C False) Lin))

smiles6 str@(c::cs) x2 x1 x0 =
  case c of
    '%' => smiles8 cs x2 x1 x0
    _  => case (&&) ((<=) c '9') ((<=) '0' c) of
      True => smiles9 cs (toRingNr (toDigit c)) x2 x1 x0
      _   => smiles2 str ((:<) x0 (TA x1 x2))
smiles6 [] x2 x1 x0 = smiles2 Nil ((:<) x0 (TA x1 x2))

smiles7 str@(c::cs) x0 =
  case c of
    '0' => smiles11 cs (refineMassNr (cast 0)) x0
    _  => case (&&) ((<=) c '9') ((<=) '1' c) of
      True => smiles12 cs (toDigit c) x0
      _   => smiles11 str Nothing x0
smiles7 [] x0 = smiles11 Nil Nothing x0

smiles8 str@(c::cs) x2 x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => smiles10 cs (toDigit c) x2 x1 x0
    _    => Left (cast (Unexpected c))
smiles8 [] x2 x1 x0 = Left (cast EOI)

smiles9 str@(c::cs) x3 x2 x1 x0 =
  case c of
    '#' => smiles6 cs ((:<) x2 (R x3 (Just Trpl))) x1 x0
    '$' => smiles6 cs ((:<) x2 (R x3 (Just Quad))) x1 x0
    '-' => smiles6 cs ((:<) x2 (R x3 (Just Sngl))) x1 x0
    '/' => smiles6 cs ((:<) x2 (R x3 (Just FW))) x1 x0
    ':' => smiles6 cs ((:<) x2 (R x3 (Just Arom))) x1 x0
    '=' => smiles6 cs ((:<) x2 (R x3 (Just Dbl))) x1 x0
    '\\' => smiles6 cs ((:<) x2 (R x3 (Just BW))) x1 x0
    _   => smiles6 str ((:<) x2 (R x3 Nothing)) x1 x0
smiles9 [] x3 x2 x1 x0 = smiles6 Nil ((:<) x2 (R x3 Nothing)) x1 x0

smiles10 str@(c::cs) x3 x2 x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => smiles9 cs (toRingNr ((+) ((*) x3 10) (toDigit c))) x2 x1 x0
    _    => Left (cast (Unexpected c))
smiles10 [] x3 x2 x1 x0 = Left (cast EOI)

smiles11 str@(c::cs) x1 x0 =
  case c of
    'A' => smiles13 cs x1 x0
    'B' => smiles14 cs x1 x0
    'C' => smiles15 cs x1 x0
    'D' => smiles16 cs x1 x0
    'E' => smiles17 cs x1 x0
    'F' => smiles18 cs x1 x0
    'G' => smiles19 cs x1 x0
    'H' => smiles20 cs x1 x0
    'I' => smiles21 cs x1 x0
    'K' => smiles22 cs x1 x0
    'L' => smiles23 cs x1 x0
    'M' => smiles24 cs x1 x0
    'N' => smiles25 cs x1 x0
    'O' => smiles26 cs x1 x0
    'P' => smiles27 cs x1 x0
    'R' => smiles28 cs x1 x0
    'S' => smiles29 cs x1 x0
    'T' => smiles30 cs x1 x0
    'U' => smiles31 cs (MkAI U x1 False) x0
    'V' => smiles31 cs (MkAI V x1 False) x0
    'W' => smiles31 cs (MkAI W x1 False) x0
    'X' => smiles32 cs x1 x0
    'Y' => smiles33 cs x1 x0
    'Z' => smiles34 cs x1 x0
    _   => Left (cast (Unexpected c))
smiles11 [] x1 x0 = Left (cast EOI)

smiles12 str@(c::cs) x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => smiles12 cs ((+) ((*) x1 10) (toDigit c)) x0
    _    => smiles11 str (refineMassNr (cast x1)) x0
smiles12 [] x1 x0 = smiles11 Nil (refineMassNr (cast x1)) x0

smiles13 str@(c::cs) x1 x0 =
  case c of
    'c' => smiles31 cs (MkAI Ac x1 False) x0
    'g' => smiles31 cs (MkAI Ag x1 False) x0
    'l' => smiles31 cs (MkAI Al x1 False) x0
    'm' => smiles31 cs (MkAI Am x1 False) x0
    'r' => smiles31 cs (MkAI Ar x1 False) x0
    's' => smiles31 cs (MkAI As x1 False) x0
    't' => smiles31 cs (MkAI At x1 False) x0
    'u' => smiles31 cs (MkAI Au x1 False) x0
    _   => Left (cast (Unexpected c))
smiles13 [] x1 x0 = Left (cast EOI)

smiles14 str@(c::cs) x1 x0 =
  case c of
    '@' => smiles36 cs (MkAI B x1 False) x0
    'A' => smiles37 cs (MkAI B x1 False) x0
    'S' => smiles38 cs (MkAI B x1 False) x0
    'T' => smiles39 cs (MkAI B x1 False) x0
    'a' => smiles31 cs (MkAI Ba x1 False) x0
    'e' => smiles31 cs (MkAI Be x1 False) x0
    'h' => smiles31 cs (MkAI Bh x1 False) x0
    'i' => smiles31 cs (MkAI Bi x1 False) x0
    'k' => smiles31 cs (MkAI Bk x1 False) x0
    'r' => smiles31 cs (MkAI Br x1 False) x0
    _   => smiles35 str (MkAI B x1 False) None x0
smiles14 [] x1 x0 = smiles35 Nil (MkAI B x1 False) None x0

smiles15 str@(c::cs) x1 x0 =
  case c of
    '@' => smiles36 cs (MkAI C x1 False) x0
    'A' => smiles37 cs (MkAI C x1 False) x0
    'S' => smiles38 cs (MkAI C x1 False) x0
    'T' => smiles39 cs (MkAI C x1 False) x0
    'a' => smiles31 cs (MkAI Ca x1 False) x0
    'd' => smiles31 cs (MkAI Cd x1 False) x0
    'e' => smiles31 cs (MkAI Ce x1 False) x0
    'f' => smiles31 cs (MkAI Cf x1 False) x0
    'l' => smiles31 cs (MkAI Cl x1 False) x0
    'm' => smiles31 cs (MkAI Cm x1 False) x0
    'n' => smiles31 cs (MkAI Cn x1 False) x0
    'o' => smiles31 cs (MkAI Co x1 False) x0
    'r' => smiles31 cs (MkAI Cr x1 False) x0
    's' => smiles31 cs (MkAI Cs x1 False) x0
    'u' => smiles31 cs (MkAI Cu x1 False) x0
    _   => smiles35 str (MkAI C x1 False) None x0
smiles15 [] x1 x0 = smiles35 Nil (MkAI C x1 False) None x0

smiles16 str@(c::cs) x1 x0 =
  case c of
    'b' => smiles31 cs (MkAI Db x1 False) x0
    's' => smiles31 cs (MkAI Ds x1 False) x0
    'y' => smiles31 cs (MkAI Dy x1 False) x0
    _   => Left (cast (Unexpected c))
smiles16 [] x1 x0 = Left (cast EOI)

smiles17 str@(c::cs) x1 x0 =
  case c of
    'r' => smiles31 cs (MkAI Er x1 False) x0
    's' => smiles31 cs (MkAI Es x1 False) x0
    'u' => smiles31 cs (MkAI Eu x1 False) x0
    _   => Left (cast (Unexpected c))
smiles17 [] x1 x0 = Left (cast EOI)

smiles18 str@(c::cs) x1 x0 =
  case c of
    '@' => smiles36 cs (MkAI F x1 False) x0
    'A' => smiles37 cs (MkAI F x1 False) x0
    'S' => smiles38 cs (MkAI F x1 False) x0
    'T' => smiles39 cs (MkAI F x1 False) x0
    'e' => smiles31 cs (MkAI Fe x1 False) x0
    'l' => smiles31 cs (MkAI Fl x1 False) x0
    'm' => smiles31 cs (MkAI Fm x1 False) x0
    'r' => smiles31 cs (MkAI Fr x1 False) x0
    _   => smiles35 str (MkAI F x1 False) None x0
smiles18 [] x1 x0 = smiles35 Nil (MkAI F x1 False) None x0

smiles19 str@(c::cs) x1 x0 =
  case c of
    'a' => smiles31 cs (MkAI Ga x1 False) x0
    'd' => smiles31 cs (MkAI Gd x1 False) x0
    'e' => smiles31 cs (MkAI Ge x1 False) x0
    _   => Left (cast (Unexpected c))
smiles19 [] x1 x0 = Left (cast EOI)

smiles20 str@(c::cs) x1 x0 =
  case c of
    '@' => smiles36 cs (MkAI H x1 False) x0
    'A' => smiles37 cs (MkAI H x1 False) x0
    'S' => smiles38 cs (MkAI H x1 False) x0
    'T' => smiles39 cs (MkAI H x1 False) x0
    'e' => smiles31 cs (MkAI He x1 False) x0
    'f' => smiles31 cs (MkAI Hf x1 False) x0
    'g' => smiles31 cs (MkAI Hg x1 False) x0
    'o' => smiles31 cs (MkAI Ho x1 False) x0
    's' => smiles31 cs (MkAI Hs x1 False) x0
    _   => smiles35 str (MkAI H x1 False) None x0
smiles20 [] x1 x0 = smiles35 Nil (MkAI H x1 False) None x0

smiles21 str@(c::cs) x1 x0 =
  case c of
    '@' => smiles36 cs (MkAI I x1 False) x0
    'A' => smiles37 cs (MkAI I x1 False) x0
    'S' => smiles38 cs (MkAI I x1 False) x0
    'T' => smiles39 cs (MkAI I x1 False) x0
    'n' => smiles31 cs (MkAI In x1 False) x0
    'r' => smiles31 cs (MkAI Ir x1 False) x0
    _   => smiles35 str (MkAI I x1 False) None x0
smiles21 [] x1 x0 = smiles35 Nil (MkAI I x1 False) None x0

smiles22 str@(c::cs) x1 x0 =
  case c of
    '@' => smiles36 cs (MkAI K x1 False) x0
    'A' => smiles37 cs (MkAI K x1 False) x0
    'S' => smiles38 cs (MkAI K x1 False) x0
    'T' => smiles39 cs (MkAI K x1 False) x0
    'r' => smiles31 cs (MkAI Kr x1 False) x0
    _   => smiles35 str (MkAI K x1 False) None x0
smiles22 [] x1 x0 = smiles35 Nil (MkAI K x1 False) None x0

smiles23 str@(c::cs) x1 x0 =
  case c of
    'a' => smiles31 cs (MkAI La x1 False) x0
    'i' => smiles31 cs (MkAI Li x1 False) x0
    'r' => smiles31 cs (MkAI Lr x1 False) x0
    'u' => smiles31 cs (MkAI Lu x1 False) x0
    'v' => smiles31 cs (MkAI Lv x1 False) x0
    _   => Left (cast (Unexpected c))
smiles23 [] x1 x0 = Left (cast EOI)

smiles24 str@(c::cs) x1 x0 =
  case c of
    'c' => smiles31 cs (MkAI Mc x1 False) x0
    'd' => smiles31 cs (MkAI Md x1 False) x0
    'g' => smiles31 cs (MkAI Mg x1 False) x0
    'n' => smiles31 cs (MkAI Mn x1 False) x0
    'o' => smiles31 cs (MkAI Mo x1 False) x0
    't' => smiles31 cs (MkAI Mt x1 False) x0
    _   => Left (cast (Unexpected c))
smiles24 [] x1 x0 = Left (cast EOI)

smiles25 str@(c::cs) x1 x0 =
  case c of
    '@' => smiles36 cs (MkAI N x1 False) x0
    'A' => smiles37 cs (MkAI N x1 False) x0
    'S' => smiles38 cs (MkAI N x1 False) x0
    'T' => smiles39 cs (MkAI N x1 False) x0
    'a' => smiles31 cs (MkAI Na x1 False) x0
    'b' => smiles31 cs (MkAI Nb x1 False) x0
    'd' => smiles31 cs (MkAI Nd x1 False) x0
    'e' => smiles31 cs (MkAI Ne x1 False) x0
    'h' => smiles31 cs (MkAI Nh x1 False) x0
    'i' => smiles31 cs (MkAI Ni x1 False) x0
    'o' => smiles31 cs (MkAI No x1 False) x0
    'p' => smiles31 cs (MkAI Np x1 False) x0
    _   => smiles35 str (MkAI N x1 False) None x0
smiles25 [] x1 x0 = smiles35 Nil (MkAI N x1 False) None x0

smiles26 str@(c::cs) x1 x0 =
  case c of
    '@' => smiles36 cs (MkAI O x1 False) x0
    'A' => smiles37 cs (MkAI O x1 False) x0
    'S' => smiles38 cs (MkAI O x1 False) x0
    'T' => smiles39 cs (MkAI O x1 False) x0
    'g' => smiles31 cs (MkAI Og x1 False) x0
    's' => smiles31 cs (MkAI Os x1 False) x0
    _   => smiles35 str (MkAI O x1 False) None x0
smiles26 [] x1 x0 = smiles35 Nil (MkAI O x1 False) None x0

smiles27 str@(c::cs) x1 x0 =
  case c of
    '@' => smiles36 cs (MkAI P x1 False) x0
    'A' => smiles37 cs (MkAI P x1 False) x0
    'S' => smiles38 cs (MkAI P x1 False) x0
    'T' => smiles39 cs (MkAI P x1 False) x0
    'a' => smiles31 cs (MkAI Pa x1 False) x0
    'b' => smiles31 cs (MkAI Pb x1 False) x0
    'd' => smiles31 cs (MkAI Pd x1 False) x0
    'm' => smiles31 cs (MkAI Pm x1 False) x0
    'o' => smiles31 cs (MkAI Po x1 False) x0
    'r' => smiles31 cs (MkAI Pr x1 False) x0
    't' => smiles31 cs (MkAI Pt x1 False) x0
    'u' => smiles31 cs (MkAI Pu x1 False) x0
    _   => smiles35 str (MkAI P x1 False) None x0
smiles27 [] x1 x0 = smiles35 Nil (MkAI P x1 False) None x0

smiles28 str@(c::cs) x1 x0 =
  case c of
    'a' => smiles31 cs (MkAI Ra x1 False) x0
    'b' => smiles31 cs (MkAI Rb x1 False) x0
    'e' => smiles31 cs (MkAI Re x1 False) x0
    'f' => smiles31 cs (MkAI Rf x1 False) x0
    'g' => smiles31 cs (MkAI Rg x1 False) x0
    'h' => smiles31 cs (MkAI Rh x1 False) x0
    'n' => smiles31 cs (MkAI Rn x1 False) x0
    'u' => smiles31 cs (MkAI Ru x1 False) x0
    _   => Left (cast (Unexpected c))
smiles28 [] x1 x0 = Left (cast EOI)

smiles29 str@(c::cs) x1 x0 =
  case c of
    '@' => smiles36 cs (MkAI S x1 False) x0
    'A' => smiles37 cs (MkAI S x1 False) x0
    'S' => smiles38 cs (MkAI S x1 False) x0
    'T' => smiles39 cs (MkAI S x1 False) x0
    'b' => smiles31 cs (MkAI Sb x1 False) x0
    'c' => smiles31 cs (MkAI Sc x1 False) x0
    'e' => smiles31 cs (MkAI Se x1 False) x0
    'g' => smiles31 cs (MkAI Sg x1 False) x0
    'i' => smiles31 cs (MkAI Si x1 False) x0
    'm' => smiles31 cs (MkAI Sm x1 False) x0
    'n' => smiles31 cs (MkAI Sn x1 False) x0
    'r' => smiles31 cs (MkAI Sr x1 False) x0
    _   => smiles35 str (MkAI S x1 False) None x0
smiles29 [] x1 x0 = smiles35 Nil (MkAI S x1 False) None x0

smiles30 str@(c::cs) x1 x0 =
  case c of
    'a' => smiles31 cs (MkAI Ta x1 False) x0
    'b' => smiles31 cs (MkAI Tb x1 False) x0
    'c' => smiles31 cs (MkAI Tc x1 False) x0
    'e' => smiles31 cs (MkAI Te x1 False) x0
    'h' => smiles31 cs (MkAI Th x1 False) x0
    'i' => smiles31 cs (MkAI Ti x1 False) x0
    'l' => smiles31 cs (MkAI Tl x1 False) x0
    'm' => smiles31 cs (MkAI Tm x1 False) x0
    's' => smiles31 cs (MkAI Ts x1 False) x0
    _   => Left (cast (Unexpected c))
smiles30 [] x1 x0 = Left (cast EOI)

smiles31 str@(c::cs) x1 x0 =
  case c of
    '@' => smiles36 cs x1 x0
    'A' => smiles37 cs x1 x0
    'S' => smiles38 cs x1 x0
    'T' => smiles39 cs x1 x0
    _   => smiles35 str x1 None x0
smiles31 [] x1 x0 = smiles35 Nil x1 None x0

smiles32 str@(c::cs) x1 x0 =
  case c of
    'e' => smiles31 cs (MkAI Xe x1 False) x0
    _   => Left (cast (Unexpected c))
smiles32 [] x1 x0 = Left (cast EOI)

smiles33 str@(c::cs) x1 x0 =
  case c of
    '@' => smiles36 cs (MkAI Y x1 False) x0
    'A' => smiles37 cs (MkAI Y x1 False) x0
    'S' => smiles38 cs (MkAI Y x1 False) x0
    'T' => smiles39 cs (MkAI Y x1 False) x0
    'b' => smiles31 cs (MkAI Yb x1 False) x0
    _   => smiles35 str (MkAI Y x1 False) None x0
smiles33 [] x1 x0 = smiles35 Nil (MkAI Y x1 False) None x0

smiles34 str@(c::cs) x1 x0 =
  case c of
    'n' => smiles31 cs (MkAI Zn x1 False) x0
    'r' => smiles31 cs (MkAI Zr x1 False) x0
    _   => Left (cast (Unexpected c))
smiles34 [] x1 x0 = Left (cast EOI)

smiles35 str@(c::cs) x2 x1 x0 =
  case c of
    'H' => smiles41 cs x2 x1 x0
    _   => smiles40 str x2 x1 (MkHCount (fromInteger 0)) x0
smiles35 [] x2 x1 x0 = smiles40 Nil x2 x1 (MkHCount (fromInteger 0)) x0

smiles36 str@(c::cs) x1 x0 =
  case c of
    '@' => smiles35 cs x1 CCW x0
    'H' => smiles41 cs x1 CW x0
    _   => smiles40 str x1 CW (MkHCount (fromInteger 0)) x0
smiles36 [] x1 x0 = smiles40 Nil x1 CW (MkHCount (fromInteger 0)) x0

smiles37 str@(c::cs) x1 x0 =
  case c of
    'L' => smiles45 cs x1 x0
    _   => Left (cast (Unexpected c))
smiles37 [] x1 x0 = Left (cast EOI)

smiles38 str@(c::cs) x1 x0 =
  case c of
    'P' => smiles46 cs x1 x0
    _   => Left (cast (Unexpected c))
smiles38 [] x1 x0 = Left (cast EOI)

smiles39 str@(c::cs) x1 x0 =
  case c of
    'H' => smiles47 cs x1 x0
    _   => Left (cast (Unexpected c))
smiles39 [] x1 x0 = Left (cast EOI)

smiles40 str@(c::cs) x3 x2 x1 x0 =
  case c of
    '+' => smiles43 cs x3 x2 x1 x0
    '-' => smiles44 cs x3 x2 x1 x0
    _   => smiles42 str (bracket x3 x2 x1 (MkCharge (fromInteger 0))) x0
smiles40 [] x3 x2 x1 x0 = smiles42 Nil (bracket x3 x2 x1 (MkCharge (fromInteger 0))) x0

smiles41 str@(c::cs) x2 x1 x0 =
  case c of
    '+' => smiles43 cs x2 x1 (MkHCount (fromInteger 1)) x0
    '-' => smiles44 cs x2 x1 (MkHCount (fromInteger 1)) x0
    _  => case (&&) ((<=) c '9') ((<=) '1' c) of
      True => smiles40 cs x2 x1 (fromMaybe (fromInteger 0) (refineHCount (cast (toDigit c)))) x0
      _   => smiles42 str (bracket x2 x1 (MkHCount (fromInteger 1)) (MkCharge (fromInteger 0))) x0
smiles41 [] x2 x1 x0 = smiles42 Nil (bracket x2 x1 (MkHCount (fromInteger 1)) (MkCharge (fromInteger 0))) x0

smiles42 str@(c::cs) x1 x0 =
  case c of
    ']' => smiles6 cs Lin x1 x0
    _   => Left (cast (Unexpected c))
smiles42 [] x1 x0 = Left (cast EOI)

smiles43 str@(c::cs) x3 x2 x1 x0 =
  case c of
    '+' => smiles42 cs (bracket x3 x2 x1 (MkCharge (fromInteger 2))) x0
    ']' => smiles6 cs Lin (bracket x3 x2 x1 (MkCharge (fromInteger 1))) x0
    _   => Left (cast (Unexpected c))
smiles43 [] x3 x2 x1 x0 = Left (cast EOI)

smiles44 str@(c::cs) x3 x2 x1 x0 =
  case c of
    '-' => smiles42 cs (bracket x3 x2 x1 (MkCharge (fromInteger (-2)))) x0
    ']' => smiles6 cs Lin (bracket x3 x2 x1 (MkCharge (fromInteger (-1)))) x0
    _   => Left (cast (Unexpected c))
smiles44 [] x3 x2 x1 x0 = Left (cast EOI)

smiles45 str@(c::cs) x1 x0 =
  case c of
    '1' => smiles35 cs x1 AL1 x0
    '2' => smiles35 cs x1 AL2 x0
    _   => Left (cast (Unexpected c))
smiles45 [] x1 x0 = Left (cast EOI)

smiles46 str@(c::cs) x1 x0 =
  case c of
    '1' => smiles35 cs x1 SP1 x0
    '2' => smiles35 cs x1 SP2 x0
    '3' => smiles35 cs x1 SP3 x0
    _   => Left (cast (Unexpected c))
smiles46 [] x1 x0 = Left (cast EOI)

smiles47 str@(c::cs) x1 x0 =
  case c of
    '1' => smiles35 cs x1 TH1 x0
    '2' => smiles35 cs x1 TH2 x0
    _   => Left (cast (Unexpected c))
smiles47 [] x1 x0 = Left (cast EOI)



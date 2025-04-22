module Text.ILex.RExp

import Data.Bool
import Data.ByteString
import public Text.ILex.Char.Set
import public Text.ILex.Val
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Regular Expressions
--------------------------------------------------------------------------------

||| A data type for regular expressions.
|||
||| The `Bool` flag indicates, if the regular expression consumes
||| at least one character of input or not.
public export
data RExpOf : Bool -> Type -> Type where
  Eps  : RExpOf False t
  Ch   : SetOf t -> RExpOf True t
  And  : RExpOf b1 t -> RExpOf b2 t -> RExpOf (b1 || b2) t
  Or   : RExpOf b1 t -> RExpOf b2 t -> RExpOf (b1 && b2) t
  Star : RExpOf True t -> RExpOf False t

%runElab derivePattern "RExpOf" [I,P] [Show]

public export
0 RExp : Bool -> Type
RExp b = RExpOf b Bits32

public export
0 RExp8 : Bool -> Type
RExp8 b = RExpOf b Bits8

public export
data IsCh : RExpOf b t -> Type where
  ItIsCh : IsCh (Ch s)

export
adjRanges : (SetOf t -> RExpOf True s) -> RExpOf b t -> RExpOf b s
adjRanges f Eps       = Eps
adjRanges f (Ch x)    = f x
adjRanges f (And x y) = And (adjRanges f x) (adjRanges f y)
adjRanges f (Or x y)  = Or (adjRanges f x) (adjRanges f y)
adjRanges f (Star x)  = Star (adjRanges f x)

--------------------------------------------------------------------------------
-- Conv
--------------------------------------------------------------------------------

public export
data Conv : Type -> Type where
  Ignore : Conv a
  Const  : Val a -> Conv a
  Txt    : Val (ByteString -> a) -> Conv a
  Chr    : Val (Bits8 -> a) -> Conv a
  Len    : Val (Nat -> a) -> Conv a

export
Eq (Conv a) where
  Ignore   == Ignore   = True
  Const v1 == Const v2 = v1 == v2
  Txt   v1 == Txt v2   = v1 == v2
  Len   v1 == Len v2   = v1 == v2
  Chr   v1 == Chr v2   = v1 == v2
  _        == _        = False

export
Show (Conv a) where
  showPrec p Ignore    = "Ignore"
  showPrec p (Const x) = showCon p "Const" (showArg x)
  showPrec p (Txt x)   = showCon p "Txt" (showArg x)
  showPrec p (Len x)   = showCon p "Len" (showArg x)
  showPrec p (Chr x)   = showCon p "Chr" (showArg x)

export %macro
const : (0 x : a) -> Elab (Conv a)
const x = do
  v <- lift x
  pure (Const v)

export %macro
bytes : (0 x : ByteString -> a) -> Elab (Conv a)
bytes x = do
  v <- lift x
  pure (Txt v)

export %macro
char : (0 x : Bits8 -> a) -> Elab (Conv a)
char x = do
  v <- lift x
  pure (Chr v)

export %macro
count : (0 x : Nat -> a) -> Elab (Conv a)
count x = do
  v <- lift x
  pure (Len v)

public export
0 TokenMap : Type -> Type
TokenMap a = List (RExp True, Conv a)

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

public export
orF : RExpOf (b || False) t -> RExpOf b t
orF x = replace {p = \b => RExpOf b t} (orFalseNeutral b) x

public export
toOrF : RExpOf b t -> RExpOf (b || False) t
toOrF x = replace {p = \b => RExpOf b t} (sym $ orFalseNeutral b) x

--------------------------------------------------------------------------------
-- Combinators
--------------------------------------------------------------------------------

||| Accepts the given single character
public export %inline
chr : Char -> RExp True
chr = Ch . fromChar

public export %inline
fromChar : Char -> RExp True
fromChar = chr

parameters {auto bnd : Bounded t}
           {auto neg : Neg t}

  public export %inline
  not : (r : RExpOf b t) -> (0 p : IsCh r) => RExpOf True t
  not (Ch s) = Ch $ negation s

  public export %inline
  (&&) : (x,y : RExpOf b t) -> (0 p : IsCh x) => (0 q : IsCh y) => RExpOf True t
  (&&) (Ch s) (Ch t) = Ch (intersection s t)

  public export %inline
  (||) : (x,y : RExpOf b t) -> (0 p : IsCh x) => (0 q : IsCh y) => RExpOf  True t
  (||) (Ch s) (Ch t) = Ch (union s t)

  public export
  (<|>) : RExpOf b1 t -> RExpOf b2 t -> RExpOf (b1 && b2) t
  Ch x <|> Ch y = Ch (union x y)
  x <|> y       = Or x y

  public export
  oneof : (rs : List (RExpOf True t)) -> (0 p : NonEmpty rs) => RExpOf True t
  oneof [r]           = r
  oneof (r::t@(_::_)) = r <|> oneof t

public export %inline
(>>) : RExpOf b1 t -> RExpOf b2 t -> RExpOf (b1 || b2) t
(>>) = And

public export %inline
eps : RExpOf False t
eps = Eps

public export %inline
opt : RExpOf True t -> RExpOf False t
opt = (`Or` eps)

public export
chars : (cs : List Char) -> (0 p : NonEmpty cs) => RExp True
chars [c]            = chr c
chars (c::cs@(_::_)) = chr c >> chars cs

public export
str : (s : String) -> (0 p : NonEmpty (unpack s)) => RExp True
str s = chars (unpack s)

public export %inline
fromString : (s : String) -> (0 p : NonEmpty (unpack s)) => RExp True
fromString = str

public export
pre : (s : String) -> (0 p : NonEmpty (unpack s)) => RExp b -> RExp True
pre s r = str s >> r

public export %inline
star : RExpOf True t -> RExpOf False t
star = Star

public export %inline
plus : RExpOf True t -> RExpOf True t
plus x = x >> star x

public export
sep1 : (sep : RExpOf True t) -> RExpOf True t -> RExpOf True t
sep1 sep x = x >> star (sep >> x)

public export
sep : (sep : RExpOf True t) -> RExpOf True t -> RExpOf False t
sep s x = opt (sep1 s x)

--------------------------------------------------------------------------------
-- Character Classes
--------------------------------------------------------------------------------

||| Accepts only the newline character
public export %inline
nl : RExp True
nl = '\n'

||| Accepts any character in the given range
public export %inline
range : Char -> Char -> RExp True
range x y = Ch (range $ charRange x y)

||| Accepts any character in the given range
public export %inline
digit : RExp True
digit = Ch digit

public export
posdigit : RExp True
posdigit = Ch posdigit

||| Accepts any upper case character
public export %inline
upper : RExp True
upper = Ch upper

||| Accepts any lower case character
public export %inline
lower : RExp True
lower = Ch lower

||| Accepts any alphabetic character
public export %inline
alpha : RExp True
alpha = Ch alpha

||| Accepts any alpha-numeric character
public export %inline
alphaNum : RExp True
alphaNum = Ch alphaNum

public export
bindigit : RExp True
bindigit = chr '0' <|> chr '1'

public export
octdigit : RExp True
octdigit = range '0' '7'

public export
hexdigit : RExp True
hexdigit = range '0' '9' <|> range 'a' 'f' <|> range 'A' 'F'

public export %inline
control : RExp True
control = Ch control

public export %inline
dot : RExp True
dot = Ch printable

--------------------------------------------------------------------------------
-- Integers
--------------------------------------------------------------------------------

public export
binary : RExp True
binary = plus bindigit

public export
octal : RExp True
octal = plus octdigit

public export
decimal : RExp True
decimal = chr '0' <|> (posdigit >> star digit)

public export
hexadecimal : RExp True
hexadecimal = plus hexdigit

public export
natural : RExp True
natural =
  pre "0b" binary      <|>
  pre "0o" octal       <|>
  pre "0x" hexadecimal <|>
  decimal

module Text.ILex.Expr

import Data.Bool
import Derive.Prelude

import public Text.ILex.Args
import public Text.ILex.Set
import public Text.ILex.Util
import public Text.ILex.Val

%default total

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

public export
data Expr : Bool -> (e : Type) -> (is,os : Types) -> Type where
  AConv   : Conversions is os -> Expr False e is os

  AChar   : Set -> Expr True e is (is:<Char)

  AMatch  : Set -> Expr True e is is

  ASeq    : Expr b1 e is ms -> Expr b2 e ms os -> Expr (b1 || b2) e is os

  AOr     : Expr b1 e is os -> Expr b2 e is os -> Expr (b1 && b2) e is os

  ARec    : Expr True e is is -> Expr False e is is

  AFail   : Conversion is e -> Expr True e is os

--------------------------------------------------------------------------------
-- Character Classes
--------------------------------------------------------------------------------

||| Accepts the given single character
public export %inline
chr : Char -> Expr True e is (is:<Char)
chr = AChar . Chr

||| Accepts and drops the given single character
public export %inline
chr_ : Char -> Expr True e is is
chr_ = AMatch . Chr

||| Accepts any character
public export %inline
any : Expr True e is (is:<Char)
any = AChar Any

||| Accepts and drops any character
public export %inline
any_ : Expr True e is is
any_ = AMatch Any

||| Accepts characters that match the given predicate
public export %inline
pred : VPred -> Expr True e is (is:<Char)
pred p = AChar (Pred p)

||| Accepts and drops characters that match the given predicate
public export %inline
pred_ : VPred -> Expr True e is is
pred_ p = AMatch (Pred p)

||| Macro version of `pred`
export %macro
mpred : (Char -> Bool) -> Elab (Expr True e is (is:<Char))
mpred p = do
  vp <- lift p
  pure (pred vp)

||| Macro version of `pred_`
export %macro
mpred_ : (Char -> Bool) -> Elab (Expr True e is is)
mpred_ p = do
  vp <- lift p
  pure (pred_ vp)

||| Accepts any character in the given range
public export %inline
range : Char -> Char -> Expr True e is (is:<Char)
range x y =
  let vx := VPrim $ Ch x
      vy := VPrim $ Ch y
      vv := VPlain "v"
      gt := VApp (VApp (VPlain "(<=)") vx) vv
      lt := VApp (VApp (VPlain "(<=)") vv) vy
   in pred (V predTpe $ VLam "v" (VApp (VApp (VPlain "(&&)") lt) gt))

||| Accepts any character except the newline character
public export %inline
dot : Expr True e is (is:<Char)
dot = pred (mlift $ \v => v /= '\n')

||| Accepts and drops any character except the newline character
public export %inline
dot_ : Expr True e is is
dot_ = pred_ (mlift $ \v => v /= '\n')

||| Accepts any whitespace character
public export %inline
space : Expr True e is (is:<Char)
space = pred (mlift isSpace)

||| Accepts any whitespace character
public export %inline
space_ : Expr True e is is
space_ = pred_ (mlift isSpace)

||| Accepts any upper case character
public export %inline
upper : Expr True e is (is:<Char)
upper = pred (mlift isUpper)

||| Accepts any lower case character
public export %inline
lower : Expr True e is (is:<Char)
lower = pred (mlift isLower)

||| Accepts any alphabetic character
public export %inline
alpha : Expr True e is (is:<Char)
alpha = pred (mlift isAlpha)

||| Accepts any alpha-numeric character
public export %inline
alphaNum : Expr True e is (is:<Char)
alphaNum = pred (mlift isAlphaNum)

--------------------------------------------------------------------------------
-- Combinators
--------------------------------------------------------------------------------

public export
orF : Expr (b || False) e is os -> Expr b e is os
orF x = replace {p = \y => Expr y e is os} (orFalseNeutral b) x

public export
toOrF : Expr b e is os -> Expr (b || False) e is os
toOrF x = replace {p = \y => Expr y e is os} (sym $ orFalseNeutral b) x

export infixr 1 >>>,>>-,->>
export infixr 3 &&&

public export %inline
(>>>) : Expr b1 e is ms -> Expr b2 e ms os -> Expr (b1 || b2) e is os
(>>>) = ASeq

public export %inline
(<|>) : Expr b1 e is os -> Expr b2 e is os -> Expr (b1 && b2) e is os
(<|>) = AOr

public export
unexpected : Expr True LexErr (is:<Char) os
unexpected = AFail $ (CApp (CPure vunexpected) (CAt Lst))

public export
identity : Expr False e is is
identity = AConv CID

public export
arr : (f : Val (a -> b)) -> Expr False e (is:<a) (is:<b)
arr v = AConv $ mapConvs v

public export
(>>-) : Expr b1 e is (os:<a) -> Val (a -> b) ->  Expr b1 e is (os:<b)
x >>- v = orF $ x >>> arr v

public export
(->>) : Val (a -> b) -> Expr b1 e (is:<b) os ->  Expr b1 e (is:<a) os
v ->> x = arr v >>> x

public export
arr2 : (f : Val (a -> b -> c)) -> Expr False e (is:<a:<b) (is:<c)
arr2 v = AConv $ appConvs v

export %macro
marr : (f : a -> b) -> Elab (Expr False e (is:<a) (is:<b))
marr f = do
  v <- lift f
  pure (arr v)

export %macro
tarr : (f : a -> b) -> Elab (Expr False e (is:<a) (is:<b))
tarr f = do
  v <- lift f
  pure (arr v)

public export
map : (f : Val (a -> b)) -> Expr b1 e is (os:<a) -> Expr b1 e is (os:<b)
map f x = orF (x >>> arr f)

export %macro
mmap : (f : a -> b) -> Expr b1 e is (os:<a) -> Elab (Expr b1 e is (os:<b))
mmap f x = do
  v <- lift f
  pure $ map v x

public export %inline
pure : Val a -> Expr False e is (is:< a)
pure x = AConv (pureConvs x)

export %macro
mpure : (v : a) -> Elab (Expr False e is (is:< a))
mpure x = do
  v <- lift x
  pure (Expr.pure v)

public export
eoi : Expr False LexErr is is
eoi = (any >>> unexpected) <|> identity

export %macro
($>) : Expr b1 e is os -> (f : b) -> Elab (Expr b1 e is (os:<b))
($>) x f = do
  v <- lift f
  pure $ orF (x >>> Expr.pure v)

||| Flips the last two arguments in a computation
public export
flip : Expr False e (is:<s:<a) (is:<a:<s)
flip = AConv flipLast

public export
chars :
     (cs : List Char)
  -> {auto 0 p : NonEmpty cs}
  -> Expr True e is is
chars [c]            = chr_ c
chars (c::cs@(_::_)) = chr_ c >>> chars cs

public export
str :
     (s : String)
  -> {auto 0 p : NonEmpty (unpack s)}
  -> Expr True e is is
str s = chars (unpack s)

public export
pre :
     (s : String)
  -> {auto 0 p : NonEmpty (unpack s)}
  -> Expr b e is os
  -> Expr True e is os
pre s r = str s >>> r

||| Appends an argument to a computation that's just passed through
public export
last : Expr b e is os -> Expr b e (is:<a) (os:<a)
last (AConv x)  = AConv (appendConv x)
last (AChar x)  = AChar x >>> flip
last (AMatch x) = AMatch x
last (ASeq x y) = ASeq (last x) (last y)
last (AOr x y)  = AOr (last x) (last y)
last (ARec  x)  = ARec (last x)
last (AFail x)  = AFail (weakenConv x)

export
vlin : ToType a => Val (SnocList a)
vlin = V (toType (SnocList a)) (VPlain "Lin")

export
vwrap : ToType a => Val (a -> SnocList a)
vwrap = V (funType2 a (SnocList a)) (value `(\x => [<x]))

export
vsnoc : ToType a => Val (SnocList a -> a -> SnocList a)
vsnoc = V (funType3 (SnocList a) a (SnocList a)) (VPlain "(:<)")

export
vpack : ToType a => Val (SnocList a -> String)
vpack = V (funType2 (SnocList a) String) (value `(\x => pack (x <>> [])))

public export
(&&&) :
     Expr b1 e is (is:<a)
  -> Expr b2 e is (is:<b)
  -> Expr (b1 || b2) e is (is:<a:<b)
x &&& y = x >>> orF (last y >>> flip)

public export
fold1 :
     Val (s -> a -> s)
  -> Expr True e is (is:<a)
  -> Expr False e (is:<s) (is:<s)
fold1 f x = ARec (last x >>> flip >>> arr2 f)

public export
fold :
     (v : Val s)
  -> (f : Val (s -> a -> s))
  -> Expr True e is (is:<a)
  -> Expr False e is (is:<s)
fold v f x = pure v >>> fold1 f x

public export
snoc :
     {auto tt : ToType a}
  -> Expr True e is (is:<a)
  -> Expr True e (is:<SnocList a) (is:<SnocList a)
snoc x = last x >>> flip >>> arr2 vsnoc

public export
snocAll :
     {auto tt : ToType a}
  -> Expr True e is (is:<a)
  -> Expr False e (is:<SnocList a) (is:<SnocList a)
snocAll x = ARec (snoc x)

public export
many :
     {auto tt : ToType a}
  -> Expr True e is (is:<a)
  -> Expr False e is (is:<SnocList a)
many x = fold vlin vsnoc x

public export
sep1 :
     {auto tt : ToType a}
  -> (sep : Expr True e is is)
  -> Expr True e is (is:<a)
  -> Expr True e is (is:<SnocList a)
sep1 sep x = x >>> vwrap ->> snocAll (sep >>> x)

public export
sep :
     {auto tt : ToType a}
  -> (sep : Expr True e is is)
  -> Expr True e is (is:<a)
  -> Expr False e is (is:<SnocList a)
sep s x = sep1 s x <|> pure vlin

export %macro
mfold1 :
     (f : s -> a -> s)
  -> Expr True e is (is:<a)
  -> Elab (Expr False e (is:<s) (is:<s))
mfold1 f x = do
  ff <- lift f
  pure $ fold1 ff x

export %macro
mfold :
     (v : s)
  -> (f : s -> a -> s)
  -> Expr True e is (is:<a)
  -> Elab (Expr False e is (is:<s))
mfold v f x = do
  vv <- lift v
  ff <- lift f
  pure $ fold vv ff x

public export
choice :
     (es : List (Expr True e is os))
  -> {auto 0 p : NonEmpty es}
  -> Expr True e is os
choice [x]            = x
choice (x::xs@(_::_)) = x <|> choice xs

public export
vjust : ToType a => Val (a -> Maybe a)
vjust = V (funType2 a (Maybe a)) (VPlain "Just")

public export
vnothing : ToType a => Val (Maybe a)
vnothing = V (toType (Maybe a)) (VPlain "Nothing")

public export
opt : ToType a => Expr True e is (is:<a) -> Expr False e is (is:<Maybe a)
opt x = (x >>> arr vjust) <|> Expr.pure vnothing

--------------------------------------------------------------------------------
-- Zipping Tokens
--------------------------------------------------------------------------------

public export
data Exprs : Bool -> (e : type) -> (is : Types) -> (ts : LTypes) -> Type where
  Nil  : Exprs False e is []
  (::) :
       Expr b1 e is (is:<a)
    -> Exprs b2 e is xs
    -> Exprs (b1 || b2) e is (a::xs)

public export
lastAll : Exprs b e is ts -> Exprs b e (is:<a) ts
lastAll []        = []
lastAll (x :: xs) = (orF (last x >>> flip)) :: lastAll xs

public export
zip : (xs : Exprs b e is ts) -> Expr b e is (is <>< ts)
zip []      = identity
zip (x::xs) = x >>> zip (lastAll xs)

public export
zipWith : {ts : _} -> Exprs b e is ts -> Val (Fun ts r) -> Expr b e is (is:<r)
zipWith xs v = orF $ zip xs >>> AConv (convsAll ts v)

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

public export
digit : Expr True e is (is:<Integer)
digit = range '0' '9' >>> marr toDigit

public export
posdigit : Expr True e is (is:<Integer)
posdigit = range '1' '9' >>> marr toDigit

public export
bindigit : Expr True e is (is:<Integer)
bindigit = range '0' '1' >>> marr toDigit

public export
octdigit : Expr True e is (is:<Integer)
octdigit = range '0' '7' >>> marr toDigit

public export
hexdigit : Expr True e is (is:<Integer)
hexdigit =
  (range '0' '9' >>> marr toDigit) <|>
  (range 'a' 'f' >>> marr toHex)   <|>
  (range 'A' 'F' >>> marr (toHex . toLower))

public export
binary : Expr True e is (is:<Integer)
binary = bindigit >>> mfold1 (\x,y => x*2 + y) bindigit

public export
octal : Expr True e is (is:<Integer)
octal = octdigit >>> mfold1 (\x,y => x*8 + y) octdigit

public export
decimal : Expr True e is (is:<Integer)
decimal = (chr_ '0' $> 0) <|> (posdigit >>> mfold1 (\x,y => x*10 + y) digit)

public export
hexadecimal : Expr True e is (is:<Integer)
hexadecimal = (hexdigit >>> mfold1 (\x,y => x*16 + y) hexdigit)

public export
natural : Expr True e is (is:<Integer)
natural =
  pre "0b" binary      <|>
  pre "0o" octal       <|>
  pre "0x" hexadecimal <|>
  decimal

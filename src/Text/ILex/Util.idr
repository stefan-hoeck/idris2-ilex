module Text.ILex.Util

import public Data.DPair
import Data.ByteString
import Derive.Prelude
import Text.ILex.Lexer

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Reading Numbers
--------------------------------------------------------------------------------

||| Converts a string of binary digits to an integer
export
binary : ByteString -> Integer
binary (BS n bv) = go 0 n
  where
    go : Integer -> (k : Nat) -> (x : Ix k n) => Integer
    go res 0     = res
    go res (S k) =
      case ix bv k of
        48 => go (res * 2) k
        _  => go (res * 2 + 1) k

export %inline
decimaldigit : Bits8 -> Integer
decimaldigit x = cast x - 48

||| Converts a string of octal digits to an integer
export
octal : ByteString -> Integer
octal (BS n bv) = go 0 n
  where
    go : Integer -> (k : Nat) -> (x : Ix k n) => Integer
    go res 0     = res
    go res (S k) = go (res * 8 + decimaldigit (ix bv k)) k

||| Converts a string of decimal digits to an integer
export
decimal : ByteString -> Integer
decimal (BS n bv) = go 0 n
  where
    go : Integer -> (k : Nat) -> (x : Ix k n) => Integer
    go res 0     = res
    go res (S k) = go (res * 10 + decimaldigit (ix bv k)) k

export
hexdigit : Bits8 -> Integer
hexdigit x =
  if      x <= byte_9 then cast x - cast byte_0
  else if x <= byte_F then 10 + cast x - cast byte_A
  else                     10 + cast x - cast byte_a

||| Converts a string of decimal digits to an integer
export
hexadecimal : ByteString -> Integer
hexadecimal (BS n bv) = go 0 n
  where
    go : Integer -> (k : Nat) -> (x : Ix k n) => Integer
    go res 0     = res
    go res (S k) = go (res * 16 + hexdigit (ix bv k)) k

||| Converts an integer literal with optional sign prefix
||| to an integer.
export
integer : ByteString -> Integer
integer bs@(BS (S k) bv) =
  case bv `at` 0 of
    45 => negate $ decimal (BS k $ tail bv)
    43 => decimal (BS k $ tail bv)
    _  => decimal bs
integer bs = decimal bs

--------------------------------------------------------------------------------
-- Working with Lists
--------------------------------------------------------------------------------

public export
data SepTag = New | Val | Sep

%runElab derive "SepTag" [Show,Eq,Ord]

export
sep : SepTag -> a -> Bounds -> t -> StepRes e a t
sep Val v _  _   = Right v
sep _   _ bs tok = unexpected bs tok

export
val : SepTag -> a -> Bounds -> t -> StepRes e a t
val Val _ bs tok = unexpected bs tok
val _   v _  _   = Right v

export
close : SepTag -> a -> Bounds -> t -> StepRes e a t
close Sep _ bs tok = unexpected bs tok
close _   v _  _   = Right v

--------------------------------------------------------------------------------
-- Encodings
--------------------------------------------------------------------------------

||| Converts an integer to a hexadecimal digit.
|||
||| This assumes that the integer is already in the range 0 - 15.
public export
hexChar : Integer -> Char
hexChar 0 = '0'
hexChar 1 = '1'
hexChar 2 = '2'
hexChar 3 = '3'
hexChar 4 = '4'
hexChar 5 = '5'
hexChar 6 = '6'
hexChar 7 = '7'
hexChar 8 = '8'
hexChar 9 = '9'
hexChar 10 = 'a'
hexChar 11 = 'b'
hexChar 12 = 'c'
hexChar 13 = 'd'
hexChar 14 = 'e'
hexChar _  = 'f'

--------------------------------------------------------------------------------
-- Tagged Parsers
--------------------------------------------------------------------------------

||| A parsing step over a plain state.
public export
0 Step : Type -> Type -> Type -> Type
Step e s t = t -> s -> Bounds -> StepRes e s t

||| A parsing end-of-input computation over a plain state.
public export
0 EOI : Type -> Type -> Type -> Type -> Type
EOI e s t a = Bounds -> s -> StepRes e a t

||| Utility for combining a snoc-list of expressions combined
||| via left-binding operators of different fixity into a single
||| expression.
export
mergeL : Ord o => (o -> e -> e -> e) -> SnocList (e,o) -> e -> e
mergeL merge sp y =
  case sp <>> [] of
    []        => y
    (x,ox)::t => go [<] x ox t y

  where
    app : SnocList (e,o) -> e -> o -> List (e,o) -> e -> e

    go : SnocList (e,o) -> e -> o -> List (e,o) -> e -> e
    go sx x ox []        z =
      case sx of
        [<]        => merge ox x z
        sp:<(w,ow) => go sp w ow [] (merge ox x z)

    go sx x ox ((y,oy) :: xs) z =
      case compare ox oy of
        LT => go (sx:<(x,ox)) y oy xs z
        EQ => go sx (merge ox x y) oy xs z
        GT => app sx (merge ox x y) oy xs z

    app [<]                x ox xs z = go [<] x ox xs z
    app outer@(sp:<(w,ow)) x ox xs z =
      case compare ow ox of
        LT => go outer x ox xs z
        _  => app sp (merge ow w x) ox xs z

||| Utility for converting a snoc list into a list.
|||
||| This is useful when streaming chunks of data and emitting
||| all the accumulated values of a single chunk.
export
maybeList : SnocList a -> Maybe (List a)
maybeList [<] = Nothing
maybeList sx  = Just (sx <>> [])

||| Concatenates the strings accumulated in a snoc list.
|||
||| This is a utility often used when lexing or parsing
||| string literals that support various kinds of escape
||| sequences.
export
snocPack : SnocList String -> String
snocPack [<]  = ""
snocPack [<s] = s
snocPack ss   = fastConcat $ ss <>> []

--------------------------------------------------------------------------------
-- Lexing Steps
--------------------------------------------------------------------------------

public export
data Res : (strt, n : Nat) -> (e,t : Type) -> Type where
  R :
       (p,line,col : Nat)
    -> {auto x     : Ix p n}
    -> {auto 0 lt  : LT p strt}
    -> (tok        : Tok e t)
    -> Res strt n e t

  E : (p : Position) -> (err : InnerError t e) -> Res strt n e t

export %inline
apply :
     (p  : Parser e t a)
  -> (st : p.state)
  -> Tok e t
  -> Lazy ByteString
  -> Lazy Bounds
  -> Either (Bounded $ InnerError t e) p.state
apply p st tok bytes bs =
  case tok of
    Ignore  => Right st
    Const v => p.step (I v st bs)
    Txt f   => case f (toString bytes) of
      Left  x => Left $ B (Custom x) bs
      Right v => p.step (I v st bs)
    Bytes f => case f bytes of
      Left  x => Left $ B (Custom x) bs
      Right v => p.step (I v st bs)

parameters (dfa : DFA e t)
           (buf : IBuffer n)

  succ :
       (tok        : Tok e t)
    -> (p,line,col : Nat)
    -> (cur        : ByteStep dfa.states e t)
    -> {auto x     : Ix p n}
    -> {auto 0 lt  : LT p strt}
    -> Res strt n e t

  inner :
       (p,line,col : Nat)
    -> (cur        : ByteStep dfa.states e t)
    -> {auto x     : Ix p n}
    -> {auto 0 lt  : LT p strt}
    -> Res strt n e t
  inner 0     l c cur = E (P l c) EOI
  inner (S k) l c cur =
   let b  := buf `ix` k
       l2 := incLine b l
       c2 := incCol  b c
    in case cur `atByte` b of
         KeepT     => inner k l2 c2 cur
         Done y    => R k l2 c2 y
         Keep      => inner k l2 c2 cur
         Move y    => inner k l2 c2 (dfa.next `at` y)
         MoveT y z => succ z k l2 c2 (dfa.next `at` y)
         Bottom    => E (P l c) (Byte $ buf `ix` k)

  succ tok 0     l c cur = R 0 l c tok
  succ tok (S k) l c cur =
   let b  := buf `ix` k
       l2 := incLine b l
       c2 := incCol  b c
    in case cur `atByte` b of
         KeepT     => succ tok k l2 c2 cur
         Done y    => R k l2 c2 y
         Keep      => succ tok k l2 c2 cur
         Move y    => inner k l2 c2 (dfa.next `at` y)
         MoveT y z => succ z k l2 c2 (dfa.next `at` y)
         Bottom    => R (S k) l c tok

  export
  step : (p,line,col : Nat) -> (x : Ix (S p) n) => Res (S p) n e t
  step p l c =
   let cur := dfa.next `at` 0
       b   := buf `ix` p
       l2  := incLine b l
       c2  := incCol  b c
    in case cur `atByte` b of
         Done y    => R p l2 c2 y
         Move y    => inner p l2 c2 (dfa.next `at` y)
         MoveT y z => succ z p l2 c2 (dfa.next `at` y)
         KeepT     => inner p l2 c2 cur
         Keep      => inner p l2 c2 cur
         Bottom    => E (P l2 c2) (Byte b)

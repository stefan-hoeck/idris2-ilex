module Text.ILex.Util

import public Data.DPair
import Data.ByteString
import Text.ILex.Lexer

%default total

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

--------------------------------------------------------------------------------
-- Tagged Parsers
--------------------------------------------------------------------------------

||| A parsing step over a tagged state.
public export
0 EStep : Type -> (k -> Type) -> Type -> Type
EStep e s t = {0 v : k} -> t -> s v -> Bounds -> ParseRes Bounds e (Exists s) t

public export
right : {0 s : k -> Type} -> s v -> Either e (Exists s)
right v = Right (Evidence _ v)

||| A parsing end-of-input computation over a tagged state.
public export
0 EEOI : Type -> (k -> Type) -> Type -> Type -> Type
EEOI e s t a = {0 v : k} -> Bounds -> s v -> ParseRes Bounds e a t

||| Utility for generating parsers over a tagged state.
export %inline
eparser :
     {0 s : k -> Type}
  -> (init : s v)
  -> (lex  : Exists s -> DFA e t)
  -> EStep e s t
  -> EEOI e s t a
  -> Parser Bounds e t a
eparser init lex step eoi =
  P (Evidence _ init) lex (\(I tok ev bs) => step tok ev.snd bs) (\bs,ev => eoi bs ev.snd)

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

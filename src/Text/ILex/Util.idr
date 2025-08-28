module Text.ILex.Util

import Data.ByteString
import Data.Linear.Ref1
import Derive.Prelude
import Text.ILex.Bounds
import Text.ILex.Error
import Text.ILex.Parser

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
-- Operator Precedence
--------------------------------------------------------------------------------

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
-- Stateful Parsing Utilities
--------------------------------------------------------------------------------

||| An interface for handling the parser position and token bounds
||| in a set of mutable values.
public export
interface LC (0 s : Type -> Type) where
  line   : s q -> Ref q Nat
  col    : s q -> Ref q Nat

public export
interface LC s => Pos s where
  positions : s q -> Ref q (SnocList Position)

public export
interface LC s => Bnds s where
  bounds : s q -> Ref q (SnocList Bounds)


--------------------------------------------------------------------------------
-- General Utilities
--------------------------------------------------------------------------------

export %inline
writeAs : Ref q a -> a -> r -> F1 q r
writeAs ref v res t = let _ # t := write1 ref v t in res # t

export %inline
writeVal : (0 s : Type -> Type) -> (s q -> Ref q a) -> r -> a -> S1 q s r
writeVal _ f tgt v = \(stck # t) => writeAs (f stck) v tgt t

export %inline
push1 : Ref q (SnocList a) -> a -> F1' q
push1 ref v t =
 let ss # t := read1 ref t
  in write1 ref (ss:<v) t

export %inline
push : (0 s : Type -> Type) -> (s q -> Ref q (SnocList a)) -> r -> a -> S1 q s r
push _ f tgt v =
  \(stck # t) =>
    let _ # t := push1 (f stck) v t
     in tgt # t

export %inline
const : (0 s : Type -> Type) -> r -> S1 q s r
const _ v = \(_ # t) => v # t

export %inline
replace1 : Ref q a -> a -> F1 q a
replace1 ref v t =
 let s # t := read1 ref t
     _ # t := write1 ref v t
  in s # t

export %inline
getList : Ref q (SnocList a) -> F1 q (List a)
getList ref t =
 let sv # t := replace1 ref [<] t
  in (sv <>> []) # t

export %inline
getStr : Ref q (SnocList String) -> F1 q String
getStr ref t =
 let sv # t := replace1 ref [<] t
  in snocPack sv # t

--------------------------------------------------------------------------------
-- Handling positions
--------------------------------------------------------------------------------

export %inline
incCols : LC s => Nat -> s q -> F1' q
incCols n x t =
 let cl    := col x
     c # t := read1 cl t
  in write1 cl (c+n) t

export %inline
incLine : LC s => t -> S1 q s t
incLine v (x # t) =
 let ln    := line x
     l # t := read1 ln t
     _ # t := write1 ln (S l) t
     _ # t := write1 (col x) 0 t
  in v # t

export %inline
newline : LC s => (v : k) -> Step1 q e k s
newline v = Go $ incLine v

export %inline
spaces : LC s => (v : k) -> Step1 q e k s
spaces v =
  Rd $ \(B x bs t) => let _ # t := incCols (size bs) x t in v # t

--------------------------------------------------------------------------------
-- Bounds
--------------------------------------------------------------------------------

export %inline
currentPos : LC s => s q -> F1 q Position
currentPos x t =
 let l # t := read1 (line x) t
     c # t := read1 (col x) t
  in P l c # t

export %inline
popPos : Pos s => s q -> F1 q Position
popPos x t =
  case read1 (positions x) t of
    (sb:<b) # t => let _ # t := write1 (positions x) sb t in b # t
    [<]     # t => P 0 0 # t

export %inline
pushPos : Pos s => s q -> F1' q
pushPos x t =
 let l  # t := read1 (line x) t
     c  # t := read1 (col x) t
     _  # t := write1 (col x) (S c) t
  in push1 (positions x) (P l c) t

||| Recognizes the given character and uses it to update the parser state
||| as specified by `f`.
|||
||| The current column is increased by one, and a new entry is pushed onto
||| the stack of bounds.
export %inline
copen : Pos s => Char -> S1 q s r -> (RExp True, Step1 q e r s)
copen c f =
  ( chr c
  , Go $ \(p # t) => let _ # t := pushPos p t in f (p # t)
  )

||| Recognizes the given character and uses it to update the parser state
||| as specified by `f`.
|||
||| The current column is increased by one, and on `Bounds` entry
||| is popped from the stack.
export %inline
cclose : Pos s => Char -> S1 q s r -> (RExp True, Step1 q e r s)
cclose c f =
  ( chr c
  , Go $ \(p # t) =>
     let _ # t := incCols 1 p t
         _ # t := popPos p t
      in f (p # t)
  )

--------------------------------------------------------------------------------
-- Terminals
--------------------------------------------------------------------------------

||| Recognizes the given string and uses it to update the parser state
||| as specified by `f`.
|||
||| The current column is increased by the length of `v` *before* invoking `f`.
export %inline
str :
     {auto lc : LC s}
  -> (v : String)
  -> {auto 0 prf : NonEmpty (unpack v)}
  -> (f : S1 q s r)
  -> (RExp True, Step1 q e r s)
str v f =
 let len := length v
  in (str v, Go $ \(p # t) => let _ # t := incCols len p t in f (p # t))

||| Recognizes the given character and uses it to update the parser state
||| as specified by `f`.
|||
||| The current column is increased by one *before* invoking `f`.
export %inline
chr : LC s => Char -> S1 q s r -> (RExp True, Step1 q e r s)
chr c f = (chr c, Go $ \(p # t) => let _ # t := incCols 1 p t in f (p # t))

||| Like `chr` but returns the given result directly.
||| as specified by `f`.
|||
||| The current column is increased by one as with `chr`.
export %inline
chr' : LC s => Char -> r -> (RExp True, Step1 q e r s)
chr' c = chr c . const s

||| Converts the recognized token to a `String`, increases the
||| current column by its length and invokes the given state transformer.
export %inline
read : LC s => (String -> S1 q s r) -> Step1 q e r s
read f =
  Rd $ \(B st bs t) =>
   let s     := toString bs
       _ # t := incCols (length s) st t
    in f s (st # t)

||| Increases the current column by the recognized byte string's length
||| before passing it on to the given state transformer.
export %inline
conv : LC s => (ByteString -> S1 q s r) -> Step1 q e r s
conv f =
  Rd $ \(B st bs t) =>
   let _ # t := incCols (size bs) st t
    in f bs (st # t)

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

export
unexpected : LC s => List String -> s q -> ByteString -> F1 q (BoundedErr e)
unexpected strs st bs t =
 let str     := toString bs
     cur # t := currentPos st t
     end     := {column $= (+ (pred $ length str))} cur
  in case size bs of
       0 => B EOI (BS cur end) # t
       _ => case strs of
         [] => B (Unexpected str) (BS cur end) # t
         _  => B (Expected strs str) (BS cur end) # t

export
unclosed : Pos s => String -> List String -> s q -> ByteString -> F1 q (BoundedErr e)
unclosed s ss st bs t =
  case size bs of
    0 =>
     let p # t := popPos st t
      in B (Unclosed s) (BS p p) # t
    _ => unexpected ss st bs t

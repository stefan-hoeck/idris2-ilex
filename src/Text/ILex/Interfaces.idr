module Text.ILex.Interfaces

import Data.Buffer
import Data.Linear.Ref1
import Data.String
import Syntax.T1
import Text.Bounds
import Text.ILex.Char.UTF8
import Text.ILex.Parser
import Text.ILex.Util
import Text.ParseError

%hide Prelude.(>>)
%hide Prelude.(<*)
%hide Prelude.pure

%default total

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

||| An interface for mutable parser stacks `s` that facilitates
||| parsing string tokens containing escape sequences.
public export
interface HasStringLits (0 s : Type -> Type) where
  constructor MkHSL
  strings   : s q -> Ref q (SnocList String)

||| An interface for mutable parser stacks `s` that facilitates
||| parsing string tokens containing escape sequences.
public export
interface HasStack (0 s : Type -> Type) (0 a : Type) | s where
  constructor MkHS
  stack     : s q -> Ref q a

--------------------------------------------------------------------------------
-- General Utilities
--------------------------------------------------------------------------------

export %inline
go : a -> (s q => F1 q (Index r)) -> (a,Step q r s)
go x f = (x,Go $ \(x # t) => f t)

export %inline
goBS : HasBytes s => a -> (s q => ByteString -> F1 q (Index r)) -> (a,Step q r s)
goBS x f = (x, Rd $ \(x # t) => let bs # t := read1 (bytes x) t in f bs t)

export %inline
goStr : HasBytes s => a -> (s q => String -> F1 q (Index r)) -> (a,Step q r s)
goStr x f =
  ( x
  , Rd $ \(x # t) =>
     let bs # t := read1 (bytes x) t
         s      := toString bs
      in f s t
  )

||| Writes a mutable reference and returns the given result.
export %inline
writeAs : Ref q a -> a -> r -> F1 q r
writeAs ref v res = write1 ref v >> pure res

||| Appends a value to mutable reference of a snoclist.
export %inline
push1 : Ref q (SnocList a) -> a -> F1' q
push1 ref v = T1.do
 ss <- read1 ref
 write1 ref (ss:<v)

||| Drops and discards a the last entry from a snoclist
||| stored in a mutable reference.
export %inline
pop1 : Ref q (SnocList a) -> F1' q
pop1 ref =
  read1 ref >>= \case
    sv:<_ => write1 ref sv
    _     => pure ()

||| Returns the value stored in a mutable reference and
||| overwrites it with the given replacement.
export %inline
replace1 : Ref q a -> a -> F1 q a
replace1 ref v = T1.do
  s <- read1 ref
  write1 ref v
  pure s

||| Empties a mutable reference holding a snoclist and returns
||| the corresponding list.
export %inline
getList : Ref q (SnocList a) -> F1 q (List a)
getList ref = T1.do
  sv <- replace1 ref [<]
  pure (sv <>> [])

||| Returns the content of some mutable state implementing
||| `HasStack`.
export %inline
getStack : HasStack s a => (sk : s q) => F1 q a
getStack = read1 (stack sk)

||| Overwrites the content of some mutable state implementing
||| `HasStack`.
export %inline
putStack : HasStack s a => (sk : s q) => a -> F1' q
putStack = write1 (stack sk)

||| Like `putStack` but returns the given result.
export %inline
putStackAs : HasStack s a => (sk : s q) => a -> v -> F1 q v
putStackAs = writeAs (stack sk)

||| Like `putStack` but returns the given result.
export %inline
putStackAsC : Cast b v => HasStack s a => (sk : s q) => a -> b -> F1 q v
putStackAsC res = putStackAs res . cast

||| Reads and updates the stack.
export %inline
modStackAs : (0 s : _) -> HasStack s a => (sk : s q) => (a -> a) -> v -> F1 q v
modStackAs _ f v = getStack >>= \x => putStackAs (f x) v

||| Appends a value to some mutable state implementing `HasStack`.
export %inline
pushStack : HasStack s (SnocList a) => (sk : s q) => a -> F1' q
pushStack = push1 (stack sk)

||| Like `pushStack` but returns the given result.
export %inline
pushStackAs : HasStack s (SnocList a) => (sk : s q) => a -> v -> F1 q v
pushStackAs v res = pushStack v >> pure res

||| A small utility for counting down a parser and returning one
||| of two possible outcomes.
export %inline
countdown : Ref q Nat -> (ifSucc, ifZero : a) -> F1 q a
countdown ref s z t =
 let S k # t := read1 ref t | Z # t => z # t
  in writeAs ref k s t

||| A small utility for counting down a parser and returning one
||| of two possible actions.
export %inline
countdownAct : Ref q Nat -> (ifSucc, ifZero : F1 q a) -> F1 q a
countdownAct ref s z t =
 let S k # t := read1 ref t | Z # t => z t
     _   # t := write1 ref k t
  in s t

--------------------------------------------------------------------------------
-- String Literals
--------------------------------------------------------------------------------

parameters {auto sk  : s q}
           {auto pos : HasStringLits s}

  ||| Empties the `strings` field of some mutable state implementing
  ||| `HasStringLits` and returns the concatenated string literal.
  export %inline
  getStr : F1 q String
  getStr = T1.do
    sv <- replace1 (strings sk) [<]
    pure $ snocPack sv

  ||| Appends the given string to the `strings` field of some mutable
  ||| state implementing `HasStringLits`.
  export %inline
  pushStr' : String -> F1' q
  pushStr' str = push1 (strings sk) str

  ||| Appends the given string to the `strings` field of some mutable
  ||| state implementing `HasStringLits` and returns the given result.
  export %inline
  pushStr : Cast t (Index r) => t -> String -> F1 q (Index r)
  pushStr res str = T1.do
    push1 (strings sk) str
    pure (cast res)

  ||| Appends the given character to the `strings` field of some mutable
  ||| state implementing `HasStringLits` and returns the given result.
  export %inline
  pushChar : Cast t (Index r) => t -> Char -> F1 q (Index r)
  pushChar res = pushStr res . singleton

  ||| Appends the given unicode code point to the `strings` field of some mutable
  ||| state implementing `HasStringLits` and returns the given result.
  export %inline
  pushBits32 : Cast t (Index r) => t -> Bits32 -> F1 q (Index r)
  pushBits32 res = pushChar res . cast

--------------------------------------------------------------------------------
-- Streaming
--------------------------------------------------------------------------------

||| Never emits a chunk of values during streaming.
|||
||| This is for parsers that produce a single value after consuming the
||| whole input. Such a parser can still be used with the facilities
||| from ilex-streams but will only emit a single value at the end of input.
||| In general, such a parser consumes a linear amount of memory and can
||| typically not be used to process very large amounts of data.
export
noChunk : s -> F1 q (Maybe a)
noChunk _ t = (Nothing # t)

||| Extracts the values parsed so far from the parser stack
||| and emits them during streaming.
export
snocChunk : HasStack s (SnocList a) => s q -> F1 q (Maybe $ List a)
snocChunk sk = T1.do
  ss <- replace1 (stack sk) [<]
  pure (maybeList ss)

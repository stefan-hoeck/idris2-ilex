module Text.ILex.Interfaces

import Data.Buffer
import Data.Linear.Ref1
import Data.String
import Syntax.T1
import Text.ByteBounds
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

||| An interface for mutable parser stacks `s` that allow us to
||| register custom errors, which will then be raised during parsing.
public export
interface HasBBErr (0 s : Type -> Type) (0 e : Type) | s where
  constructor MkBE
  error     : s q -> Ref q (Maybe $ BBErr e)

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
go x f = (x, Run $ \(E x t) => f t)

export %inline
ign : a -> (s q => F1 q ()) -> (a,Step q r s)
ign x f = (x, Ign $ \(E x t) => f t)

export %inline
goBS : HasBytes s => a -> (s q => ByteString -> F1 q (Index r)) -> (a,Step q r s)
goBS x f = (x, Run $ \(E x t) => let bs # t := getBytes t in f bs t)

export %inline
goStr : HasBytes s => a -> (s q => String -> F1 q (Index r)) -> (a,Step q r s)
goStr x f = (x, Run $ \(E x t) => let bs # t := getBytes t in f (toString bs) t)

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
-- Bounds and Position
--------------------------------------------------------------------------------

parameters {auto sk   : s q}
           {auto hb   : HasBytes s}

  ||| Gets the absolute position of the
  ||| first byte of the current token.
  export %inline
  startPos : F1 q BytePos
  startPos = T1.do
    RB f t <- read1 (relBounds sk)
    pure $ case f of
      0 => BP (prevOffset sk)
      _ => BP (curOffset sk + f)

  ||| Gets the absolute position of the last byte of the current token.
  export %inline
  endPos : F1 q BytePos
  endPos = T1.do
    RB f t <- read1 (relBounds sk)
    pure $ BP (curOffset sk + t)

  ||| Gets the bounds of the current token.
  export %inline
  bounds : F1 q ByteBounds
  bounds = T1.do
    RB f t <- read1 (relBounds sk)
    pure $ case f of
      0 => BB (BP $ prevOffset sk) (BP $ curOffset sk + t)
      _ => BB (BP $ curOffset sk + f) (BP $ curOffset sk + t)

  ||| Computes the given value and pairs it with the token bounds.
  export %inline
  bounded : F1 q a -> F1 q (ByteBounded a)
  bounded f t =
   let bs # t := Interfaces.bounds t
       v  # t := f t
    in B v bs # t

  ||| Pairs the given value with the token bounds.
  export %inline
  bounded' : a -> F1 q (ByteBounded a)
  bounded' v t =
   let bs # t := Interfaces.bounds t
    in B v bs # t

  ||| Pushes the current byte position onto the position stack.
  |||
  ||| This is often used when ecountering some "opening token"
  ||| (such as an opening quote or parenthesis) for which we later
  ||| expect a suitable closing token. If no closing token is encountered,
  ||| we typically want to fail with an error that lists the position
  ||| of the unclosed token.
  export %inline
  pushPosition : F1' q
  pushPosition = startPos >>= push1 (positions sk)

  ||| Discards the latest entry from the positions stack.
  export %inline
  popPosition : F1' q
  popPosition = pop1 (positions sk)

  popAndGetBounds : Nat -> F1 q ByteBounds
  popAndGetBounds n =
    read1 (positions sk) >>= \case
      sb:<b => writeAs (positions sk) sb (BB b $ incLen n b)
      [<]   => pure NoBB

  ||| Returns the bounds from start to end of some "enclosed" or
  ||| quoted region of text such as an expression in parantheses
  ||| or some text in quotes.
  export %inline
  closeBounds : F1 q ByteBounds
  closeBounds = T1.do
    pe <- endPos
    read1 (positions sk) >>= \case
      sb:<b => writeAs (positions sk) sb (BB b pe)
      [<]   => pure NoBB

--------------------------------------------------------------------------------
-- Error Handling
--------------------------------------------------------------------------------

parameters {auto hae : HasBBErr s e}

  ||| Writes the given exception to the `error` field of some
  ||| mutable state and returns the given result.
  export %inline
  failWith : (sk : s q) => BBErr e -> v -> F1 q v
  failWith = writeAs (error sk) . Just

  ||| Like `failWith`, but generates the bounds of the error from the
  ||| current position and the bytes read until the error occurred.
  export %inline
  failHere : HasBytes s => (sk : s q) => InnerError e -> v -> F1 q v
  failHere x res = T1.do
    bs <- bounds
    failWith (B x bs) res

--------------------------------------------------------------------------------
-- Terminals
--------------------------------------------------------------------------------

parameters {auto hbp : HasBytes s}
           (x        : a)

  export %inline
  ignore : (s q => F1 q ()) -> (a,Step q r s)
  ignore = ign x

  export %inline
  ignore' : (a,Step q r s)
  ignore' = ign x (() #)

  export %inline
  step : (s q => F1 q (Index r)) -> (a,Step q r s)
  step = go x

  export %inline
  step' : Cast t (Index r) => t -> (a,Step q r s)
  step' x = step (pure $ cast x)

  export %inline
  bytes : (s q => ByteString -> F1 q (Index r)) -> (a,Step q r s)
  bytes f = goBS x f

  export %inline
  string : (s q => String -> F1 q (Index r)) -> (a,Step q r s)
  string f = goStr x f

  ||| Recognizes the given character(s)
  ||| and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one, and a new entry is pushed onto
  ||| the stack of bounds.
  export %inline
  opn : (s q => F1 q (Index r)) -> (a, Step q r s)
  opn f = step $ pushPosition >> f

  ||| Convenience alias for `copen . pure`.
  export %inline
  opn' : Cast t (Index r) => t -> (a, Step q r s)
  opn' v = opn $ pure (cast v)

  ||| Recognizes the given character(s) and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by `n`, and one `Position` entry
  ||| is popped from the stack.
  export %inline
  close : (s q => F1 q (Index r)) -> (a, Step q r s)
  close f = step $ popPosition >> f

  ||| Recognizes the given character(s) and uses it to
  ||| finalize and assemble a string literal.
  |||
  ||| The current column is increased by `n`, and one `Position` entry
  ||| is popped from the stack.
  export %inline
  closeStr :
       {auto hap : HasStringLits s}
    -> (s q => String -> F1 q (Index r))
    -> (a, Step q r s)
  closeStr f = close $ getStr >>= f

  ||| Recognizes the given character(s) and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one, and on `Bounds` entry
  ||| is popped from the stack.
  export %inline
  closeWithBounds : (s q => ByteBounds -> F1 q (Index r)) -> (a, Step q r s)
  closeWithBounds f = step $ closeBounds >>= f

  ||| Recognizes the given character(s) and uses it to
  ||| finalize and assemble a string literal.
  |||
  ||| The current column is increased by `n`, and one `Position` entry
  ||| is popped from the stack.
  export %inline
  closeBoundedStr :
       {auto hap : HasStringLits s}
    -> (s q => ByteBounded String -> F1 q (Index r))
    -> (a, Step q r s)
  closeBoundedStr f = closeWithBounds $ \bs => getStr >>= \s => f (B s bs)

parameters {auto hbp : HasBytes s}

  ||| Lexes a single value based on its printed form. Returns
  ||| `Nothing` in case `display` returns the empty string.
  |||
  ||| For instance, `val show soSomething True` would recognice
  ||| the token `"True"` and invoke act with `True`.
  export
  val :
       (display : a -> String)
    -> (act     : a -> Step1 q r s)
    -> (value   : a)
    -> Maybe (RExp True, Step q r s)
  val display act v =
   let f := act v
    in case unpack (display v) of
         cs@(_::_) => Just $ step (chars cs) (f %search)
         []        => Nothing

  ||| Like `val` but for a value that can be displayed in
  ||| different ways.
  export
  valN :
       (displays : a -> List String)
    -> (act      : a -> Step1 q r s)
    -> (value    : a)
    -> List (RExp True, Step q r s)
  valN displays act v =
   let f := act v
    in mapMaybe (exp f . unpack) (displays v)
  where
    exp : Step1 q r s -> List Char -> Maybe (RExp True, Step q r s)
    exp f cs@(_::_)= Just $ step (chars cs) (f %search)
    exp f [] = Nothing

  ||| Specialized version of `val` that writes the lexed value
  ||| to a predefined mutable field of the parser stack.
  export %inline
  writeVal :
       (display : a -> String)
    -> (field   : s q -> Ref q a)
    -> Index r
    -> (value   : a)
    -> Maybe (RExp True, Step q r s)
  writeVal display field res =
    val display (\v,x => writeAs (field x) v res)

  ||| Specialized version of `valN` that writes the lexed value
  ||| to a predefined mutable field of the parser stack.
  export %inline
  writeValN :
       (displays : a -> List String)
    -> (field    : s q -> Ref q a)
    -> Index r
    -> (value    : a)
    -> List (RExp True, Step q r s)
  writeValN displays field res =
    valN displays (\v,x => writeAs (field x) v res)

  ||| Applies `val` to a list of values.
  |||
  ||| Highly useful in combination with the `Finite` interface from
  ||| the idris2-finite library.
  export %inline
  vals :
       (display : a -> String)
    -> (act     : a -> Step1 q r s)
    -> List a
    -> List (RExp True, Step q r s)
  vals display = mapMaybe . val display

  ||| Like `vals` but for values that can be displayed in
  ||| several ways.
  |||
  ||| Highly useful in combination with the `Finite` interface from
  ||| the idris2-finite library.
  export %inline
  valsN :
       (displays : a -> List String)
    -> (act      : a -> Step1 q r s)
    -> List a
    -> List (RExp True, Step q r s)
  valsN displays act vs = vs >>= valN displays act

  ||| Specialized version of `vals` that writes the lexed value
  ||| to a predefined mutable field of the parser stack.
  export %inline
  writeVals :
       (display : a -> String)
    -> (field   : s q -> Ref q a)
    -> (res     : Index r)
    -> List a
    -> List (RExp True, Step q r s)
  writeVals display field = mapMaybe . writeVal display field

  ||| Specialized version of `valsN` that writes the lexed value
  ||| to a predefined mutable field of the parser stack.
  export %inline
  writeValsN :
       (displays : a -> List String)
    -> (field    : s q -> Ref q a)
    -> (res      : Index r)
    -> List a
    -> List (RExp True, Step q r s)
  writeValsN displays field res vs = vs >>= writeValN displays field res

export
jsonSpace : RExp True
jsonSpace = oneof [' ','\t','\n','\r']

export %inline
jsonSpaces : RExp True
jsonSpaces = plus jsonSpace

export %inline
jsonSpaced : HasBytes s => Steps q r s -> Steps q r s
jsonSpaced xs = ignore' jsonSpaces :: xs

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

parameters {auto he  : HasBBErr s e}
           {auto pos : HasBytes s}

  export
  raise : InnerError e -> Nat -> s q => v -> F1 q v
  raise err n res = T1.do
    ps <- startPos
    failWith (B err $ BB ps (incLen n ps)) res

  export
  unexpected : List String -> s q -> F1 q (BBErr e)
  unexpected strs sk =
    read1 (error sk) >>= \case
      Just x  => pure x
      Nothing => T1.do
       bb <- bounds
       bs <- getBytes
       case bs of
         BS 0 _  => pure (B EOI bb)
         BS 1 bv =>
          let b := bv `at` 0
              s := String.singleton (cast b)
           in case isAscii b of
                True  => pure (B (Expected strs s) bb)
                False => pure (B (InvalidByte b) bb)
         _ => pure (B (Expected strs (toString bs)) bb)

  export
  unclosed : String -> s q -> F1 q (BBErr e)
  unclosed str sk = T1.do
    bnds <- popAndGetBounds (length str)
    pure $ B (Unclosed str) bnds

  ||| Fails with `unclosed` if this is the end of input, otherwise
  ||| invokes `unexpected`.
  export
  unclosedIfEOI : String -> List String -> s q -> F1 q (BBErr e)
  unclosedIfEOI s ss sk =
    getBytes >>= \case
      BS 0 _ => unclosed s sk
      bs     => unexpected ss sk

  ||| Fails with `unclosed` if this is the end of input or
  ||| a linefeed character (`\n`, byte `0x0a`) was encountered,
  ||| otherwise, invokes `unexpected`.
  export
  unclosedIfNLorEOI : String -> List String -> s q -> F1 q (BBErr e)
  unclosedIfNLorEOI s ss sk =
    getBytes >>= \case
      BS 0 _ => unclosed s sk
      bs     => if elem 0x0a bs then unclosed s sk else unexpected ss sk

  export %inline
  errs :
       {n : _}
    -> List (Entry n $ s q -> F1 q (BBErr e))
    -> Arr32 n (s q -> F1 q (BBErr e))
  errs = arr32 n (unexpected [])

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

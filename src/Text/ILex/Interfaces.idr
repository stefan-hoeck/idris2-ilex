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

||| An interface for mutable parser stacks `s` that allows us to keep
||| track of the current position (line and column) in the currently
||| parsed string.
public export
interface HasPosition (0 s : Type -> Type) where
  constructor MkHP
  line      : s q -> Ref q Nat
  col       : s q -> Ref q Nat
  positions : s q -> Ref q (SnocList Position)

||| An interface for mutable parser stacks `s` that allow us to
||| register custom errors, which will then be raised during parsing.
public export
interface HasError (0 s : Type -> Type) (0 e : Type) | s where
  constructor MkHE
  error     : s q -> Ref q (Maybe $ BoundedErr e)

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
-- Bounds and Position
--------------------------------------------------------------------------------

parameters {auto sk  : s q}
           {auto pos : HasPosition s}

  ||| Gets the current text position (line and column) from some
  ||| mutable state implementing `HasPosition`.
  export %inline
  getPosition : F1 q Position
  getPosition = T1.do
    l <- read1 (line sk)
    c <- read1 (col sk)
    pure $ P l c

  ||| Increases the text column of some mutable state implementing
  ||| `HasPosition` by the given amount.
  export %inline
  inccol : Nat -> F1 q ()
  inccol n = let c := col sk in read1 c >>= write1 c . (n+)

  ||| Increases the text column of some mutable state implementing
  ||| `HasPosition` by the given amount.
  export %inline
  setcol : Nat -> F1 q ()
  setcol n = write1 (col sk) n

  ||| Increases the line of some mutable state implementing
  ||| `HasPosition` by the given amount. The column field is
  ||| reset to zero.
  export %inline
  incline : Nat -> F1 q ()
  incline n = T1.do
    l <- read1 (line sk)
    write1 (line sk) (n + l)
    write1 (col sk) 0

  ||| Increases the current text position according to the characters
  ||| encountered in the given byte string.
  |||
  ||| See also `Text.ILex.Bounds.inBytes`.
  export %inline
  incML : ByteString -> F1 q ()
  incML bs = T1.do
    p <- getPosition
    let P l c := incBytes bs p
    write1 (line sk) l
    write1 (col sk) c

  ||| Gets the current token bounds from some
  ||| mutable state implementing `HasPosition` after
  ||| increasing the column by `n` characters.
  export %inline
  tokenBounds : Nat -> F1 q Bounds
  tokenBounds n = T1.do
    sp <- getPosition
    inccol n
    ep <- getPosition
    pure (BS sp ep)

  ||| Pushes the current text position onto the position stack.
  |||
  ||| This is often used when ecountering some "opening token"
  ||| (such as an opening quote or parenthesis) for which we later
  ||| expect a suitable closing token. If no closing token is encountered,
  ||| we typically want to fail with an error that lists the position
  ||| of the unclosed token.
  export %inline
  pushPosition : F1' q
  pushPosition = getPosition >>= push1 (positions sk)

  ||| Discards the latest entry from the positions stack.
  export %inline
  popPosition : F1' q
  popPosition = pop1 (positions sk)

  popAndGetBounds : Nat -> F1 q Bounds
  popAndGetBounds n =
    read1 (positions sk) >>= \case
      sb:<b => writeAs (positions sk) sb (BS b $ addCol n b)
      [<]   => pure NoBounds

  ||| Returns the bounds from start to end of some "enclosed" or
  ||| quoted region of text such as an expression in parantheses
  ||| or some text in quotes.
  export %inline
  closeBounds : F1 q Bounds
  closeBounds = T1.do
    pe <- getPosition
    read1 (positions sk) >>= \case
      sb:<b => writeAs (positions sk) sb (BS b pe)
      [<]   => pure NoBounds

parameters {auto pos : HasPosition s}

  ||| Recognizes the given expression and invokes `incline` before
  ||| returning the given result.
  export %inline
  newline : RExpOf True b -> (v : s q => F1 q (Index r)) -> (RExpOf True b, Step q r s)
  newline x f = go x $ f <* incline 1

  ||| Convenience alias for `newline x (pure v)`.
  export %inline
  newline' : Cast t (Index r) => RExpOf True b -> t -> (RExpOf True b, Step q r s)
  newline' x v = go x $ incline 1 >> pure (cast v)

  ||| Recognizes the given expression and invokes `incline n` before
  ||| returning the given result.
  export %inline
  newlines :
       Nat
    -> RExpOf True b
    -> (v : s q => F1 q (Index r))
    -> (RExpOf True b, Step q r s)
  newlines n x f = go x $ f <* incline n

  ||| Convenience alias for `newlines n x (pure v)`.
  export %inline
  newlines' : Nat -> RExpOf True b -> (v : Index r) -> (RExpOf True b, Step q r s)
  newlines' n x v = go x $ incline n >> pure v

  ||| Recognizes the given expression, increasing the line count by the given
  ||| number and setting the current column to the given value *after* invoming
  ||| the given action.
  export
  linecol :
       (line,col : Nat)
    -> RExpOf True b
    -> (v : s q => F1 q (Index r))
    -> (RExpOf True b, Step q r s)
  linecol l c x f = go x $ f <* incline l <* setcol c

  ||| Convenience alias for `linecol line col x (pure v)`.
  export
  linecol' : (line,col : Nat) -> RExpOf True b -> Index r -> (RExpOf True b, Step q r s)
  linecol' l c x v = go x $ incline l >> setcol c >> pure v

parameters {auto hae : HasError s e}

  ||| Writes the given exception to the `error` field of some
  ||| mutable state and returns the given result.
  export %inline
  failWith : (sk : s q) => BoundedErr e -> v -> F1 q v
  failWith = writeAs (error sk) . Just

  ||| Like `failWith`, but generates the bounds of the error from the
  ||| current position and the bytes read until the error occurred.
  export %inline
  failHere : HasBytes s => HasPosition s => (sk : s q) => InnerError e -> v -> F1 q v
  failHere x res = T1.do
    p  <- getPosition
    bs <- read1 (bytes sk)
    failWith (B x $ BS p (incBytes bs p)) res

--------------------------------------------------------------------------------
-- Constant-Size Terminals
--------------------------------------------------------------------------------

parameters (x          : RExpOf True b)
           {n          : Nat}
           {auto 0 prf : ConstSize n x}
           {auto   pos : HasPosition s}

  ||| Recognizes the given character and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by `n` *before* invoking `f`.
  export %inline
  cexpr : (s q => F1 q (Index r)) -> (RExpOf True b, Step q r s)
  cexpr f = go x $ inccol n >> f

  ||| Convenience alias for `cexpr . pure`.
  export %inline
  cexpr' : Cast t (Index r) => t -> (RExpOf True b, Step q r s)
  cexpr' v = cexpr $ pure (cast v)

  ||| Recognizes the given character(s)
  ||| and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one, and a new entry is pushed onto
  ||| the stack of bounds.
  export %inline
  copen : (s q => F1 q (Index r)) -> (RExpOf True b, Step q r s)
  copen f = go x $ pushPosition >> inccol n >> f

  ||| Convenience alias for `copen . pure`.
  export %inline
  copen' : Cast t (Index r) => t -> (RExpOf True b, Step q r s)
  copen' v = copen $ pure (cast v)

  ||| Recognizes the given character(s) and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by `n`, and one `Position` entry
  ||| is popped from the stack.
  export %inline
  cclose : (s q => F1 q (Index r)) -> (RExpOf True b, Step q r s)
  cclose f = go x $ inccol n >> popPosition >> f

  ||| Recognizes the given character(s) and uses it to
  ||| finalize and assemble a string literal.
  |||
  ||| The current column is increased by `n`, and one `Position` entry
  ||| is popped from the stack.
  export %inline
  ccloseStr :
       {auto hap : HasStringLits s}
    -> (s q => String -> F1 q (Index r))
    -> (RExpOf True b, Step q r s)
  ccloseStr f = cclose $ getStr >>= f

  ||| Recognizes the given character(s) and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one, and on `Bounds` entry
  ||| is popped from the stack.
  export %inline
  ccloseWithBounds : (s q => Bounds -> F1 q (Index r)) -> (RExpOf True b, Step q r s)
  ccloseWithBounds f = go x $ inccol {q} n >> closeBounds >>= f

  ||| Recognizes the given character(s) and uses it to
  ||| finalize and assemble a string literal.
  |||
  ||| The current column is increased by `n`, and one `Position` entry
  ||| is popped from the stack.
  export %inline
  ccloseBoundedStr :
       {auto hap : HasStringLits s}
    -> (s q => Bounded String -> F1 q (Index r))
    -> (RExpOf True b, Step q r s)
  ccloseBoundedStr f = ccloseWithBounds $ \bs => getStr >>= \s => f (B s bs)

parameters {auto pos : HasPosition s}

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
         cs@(_::_) =>
          let 0 prf := charsConstSize cs
           in Just $ cexpr (chars cs) (\t => f (%search # t))
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
    exp f cs@(_::_)=
     let 0 prf := charsConstSize cs
      in Just $ cexpr (chars cs) (\t => f (%search # t))
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
    val display (\v => \(x # t) => writeAs (field x) v res t)

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
    valN displays (\v => \(x # t) => writeAs (field x) v res t)

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

--------------------------------------------------------------------------------
-- String Terminals
--------------------------------------------------------------------------------

parameters (x        : RExpOf True b)
           {auto pos : HasPosition s}
           {auto pos : HasBytes s}

  ||| Converts the recognized token to a `String`, increases the
  ||| current column by its length and invokes the given state transformer.
  export %inline
  read : (s q => String -> F1 q (Index r)) -> (RExpOf True b, Step q r s)
  read f = goStr x $ \s => f s <* inccol (length s)

  ||| Increases the current line by one after invoking the given
  ||| state transformer.
  export %inline
  readline : (s q => String -> F1 q (Index r)) -> (RExpOf True b, Step q r s)
  readline f = goStr x $ \s => f s <* incline 1

  ||| Convenience alias for `read . pure`
  ||| current column by its length after invoking the given state transformer.
  export %inline
  read' : Cast t (Index r) => t -> (RExpOf True b, Step q r s)
  read' v =
    ( x
    , Rd $ \(sk # t) =>
      let bs # t := read1 (bytes sk) t
          _  # t := inccol (length $ toString bs) t
       in cast v # t
    )

  ||| Increases the current column by the length of the byte string
  ||| and invokes the given state transformer.
  export %inline
  conv : (s q => ByteString -> F1 q (Index r)) -> (RExpOf True b, Step q r s)
  conv f = goBS x $ \bs => f bs <* inccol (size bs)

  ||| Increases the current line by one after invoking the given
  ||| state transformer.
  export %inline
  convline : (s q => ByteString -> F1 q (Index r)) -> (RExpOf True b, Step q r s)
  convline f = goBS x $ \bs => f bs <* incline 1

  ||| Like `conv` but can handle byte sequence with an unknown number
  ||| of line feed characters.
  |||
  ||| Note: In performance critical parsers, this should be avoided whenever
  |||       possible. Advancing token bounds by inspecting every byte a second
  |||       time *can* have an impact. Whenever possible, try to separate your
  |||       lexems into those which consist of no line breaks and those which
  |||       consist of a predefine (typically only one) number of line breaks.
  export %inline
  multiline : (s q => ByteString -> F1 q (Index r)) -> (RExpOf True b, Step q r s)
  multiline f = goBS x $ \bs => f bs <* incML bs

  ||| Convenience alias for `conv . pure`.
  export %inline
  conv' : Cast t (Index r) => t -> (RExpOf True b, Step q r s)
  conv' v =
    ( x
    , Rd $ \(sk # t) =>
       let bs # t := read1 (bytes sk) t
           _  # t := inccol (size bs) t
        in cast v # t
    )

  ||| Convenience alias for `convML . pure`.
  |||
  ||| Please not, that the same performance considerations as for `convML`
  ||| apply.
  export %inline
  multiline' : Index r -> (RExpOf True b, Step q r s)
  multiline' v =
    ( x
    , Rd $ \(sk # t) =>
       let bs # t := read1 (bytes sk) t
           _  # t := incML bs t
        in v # t
    )

export %inline
jsonSpaced :
     {auto hp : HasPosition s}
  -> {auto hb : HasBytes s}
  -> {auto cs : Cast b (Index r)}
  -> b
  -> Steps q r s
  -> Steps q r s
jsonSpaced v xs =
  [ conv' (plus $ oneof [' ','\t']) v
  , newline' ('\n' <|> '\r' <|> "\r\n") v
  ] ++ xs

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

parameters {auto he  : HasError s e}
           {auto pos : HasPosition s}
           {auto pos : HasBytes s}

  export
  raise : InnerError e -> Nat -> s q => v -> F1 q v
  raise err n res = T1.do
    ps <- getPosition
    let bs := BS ps (addCol n ps)
    failWith (B err bs) res

  export
  unexpected : List String -> s q -> F1 q (BoundedErr e)
  unexpected strs sk =
    read1 (error sk) >>= \case
      Just x  => pure x
      Nothing => T1.do
       bs <- read1 (bytes sk)
       ps <- getPosition
       let bnds1 := BS ps $ incCol ps
       case bs of
         BS 0 _  => pure (B EOI bnds1)
         BS 1 bv =>
          let b := bv `at` 0
              s := String.singleton (cast b)
           in case isAscii b of
                True  => pure (B (Expected strs s) bnds1)
                False => pure (B (InvalidByte b) bnds1)
         bs =>
          let str  := toString bs
              bnds := BS ps (incBytes bs ps)
           in pure (B (Expected strs str) bnds)

  export
  unclosed : String -> s q -> F1 q (BoundedErr e)
  unclosed str sk = T1.do
    bnds <- popAndGetBounds (length str)
    pure $ B (Unclosed str) bnds

  ||| Fails with `unclosed` if this is the end of input, otherwise
  ||| invokes `unexpected`.
  export
  unclosedIfEOI : String -> List String -> s q -> F1 q (BoundedErr e)
  unclosedIfEOI s ss sk =
    read1 (bytes sk) >>= \case
      BS 0 _ => unclosed s sk
      _      => unexpected ss sk

  ||| Fails with `unclosed` if this is the end of input or
  ||| a linefeed character (`\n`, byte `0x0a`) was encountered,
  ||| otherwise, invokes `unexpected`.
  export
  unclosedIfNLorEOI : String -> List String -> s q -> F1 q (BoundedErr e)
  unclosedIfNLorEOI s ss sk =
    read1 (bytes sk) >>= \case
      BS 0 _ => unclosed s sk
      bs     => if elem 0x0a bs then unclosed s sk else unexpected ss sk

  export %inline
  errs :
       {n : _}
    -> List (Entry n $ s q -> F1 q (BoundedErr e))
    -> Arr32 n (s q -> F1 q (BoundedErr e))
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

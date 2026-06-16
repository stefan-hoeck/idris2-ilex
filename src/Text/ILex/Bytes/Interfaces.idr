module Text.ILex.Bytes.Interfaces

import Data.Linear.Ref1
import Data.String
import Syntax.T1
import Text.ILex.Char.UTF8
import public Text.ByteBounds
import public Text.ILex.Interfaces
import public Text.ILex.Parser

%default total

||| An interface for mutable parser stacks `s` that allows us to keep
||| track of the current byte position.
public export
interface HasBytePos (0 s : Type -> Type) where
  constructor MkHBP
  pos       : s q -> Ref q BytePos
  positions : s q -> Ref q (SnocList BytePos)

||| An interface for mutable parser stacks `s` that allow us to
||| register custom errors, which will then be raised during parsing.
public export
interface HasBBErr (0 s : Type -> Type) (0 e : Type) | s where
  constructor MkBE
  error     : s q -> Ref q (Maybe $ BBErr e)

--------------------------------------------------------------------------------
-- Bounds and Position
--------------------------------------------------------------------------------

parameters {auto sk   : s q}
           {auto hpos : HasBytePos s}

  ||| Gets the current text position (line and column) from some
  ||| mutable state implementing `HasBytePos`.
  export %inline
  bytePos : F1 q BytePos
  bytePos = read1 (pos sk)

  export %inline
  incPos : HasBytes s => F1' q
  incPos = T1.do
    bs <- read1 (bytes sk)
    mod1 (pos sk) (inc bs.size)

  export %inline
  byteBounds : HasBytes s => F1 q ByteBounds
  byteBounds = T1.do
    s  <- bytePos
    bs <- read1 (bytes sk)
    pure $ BB s (inc bs.size s)

  ||| Pushes the current byte position onto the position stack.
  |||
  ||| This is often used when ecountering some "opening token"
  ||| (such as an opening quote or parenthesis) for which we later
  ||| expect a suitable closing token. If no closing token is encountered,
  ||| we typically want to fail with an error that lists the position
  ||| of the unclosed token.
  export %inline
  pushPosition : F1' q
  pushPosition = bytePos >>= push1 (positions sk)

  ||| Discards the latest entry from the positions stack.
  export %inline
  popPosition : F1' q
  popPosition = pop1 (positions sk)

  popAndGetBounds : Nat -> F1 q ByteBounds
  popAndGetBounds n =
    read1 (positions sk) >>= \case
      sb:<b => writeAs (positions sk) sb (BB b $ inc n b)
      [<]   => pure NoBB

  ||| Returns the bounds from start to end of some "enclosed" or
  ||| quoted region of text such as an expression in parantheses
  ||| or some text in quotes.
  export %inline
  closeBounds : F1 q ByteBounds
  closeBounds = T1.do
    pe <- bytePos
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
  failHere : HasBytes s => HasBytePos s => (sk : s q) => InnerError e -> v -> F1 q v
  failHere x res = T1.do
    bs <- byteBounds
    failWith (B x bs) res

--------------------------------------------------------------------------------
-- Terminals
--------------------------------------------------------------------------------

parameters {auto hbp : HasBytePos s}
           {auto hbs : HasBytes s}
           (x        : a)

  export %inline
  ignore : (s q => F1 q ()) -> (a,Step q r s)
  ignore f = ign x $ \t => let _ # t := f t in incPos t

  export %inline
  ignore' : (a,Step q r s)
  ignore' = ign x incPos

  export %inline
  step : (s q => F1 q (Index r)) -> (a,Step q r s)
  step f =
    go x $ \t =>
     let res # t := f t
         _   # t := incPos t
      in res # t

  export %inline
  step' : Cast t (Index r) => t -> (a,Step q r s)
  step' x = step (pure $ cast x)

  export %inline
  bytes : (s q => ByteString -> F1 q (Index r)) -> (a,Step q r s)
  bytes f =
    goBS x $ \bs,t =>
     let res # t := f bs t
         _   # t := mod1 (pos {s} %search) (inc bs.size) t
      in res # t

  export %inline
  string : (s q => String -> F1 q (Index r)) -> (a,Step q r s)
  string f = bytes $ \bs,t => f (toString bs) t

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

parameters {auto hbp : HasBytePos s}
           {auto hbs : HasBytes s}

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
           in Just $ step (chars cs) (f %search)
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
      in Just $ step (chars cs) (f %search)
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
jsonSpaced :
     {auto hp : HasBytePos s}
  -> {auto hb : HasBytes s}
  -> Steps q r s
  -> Steps q r s
jsonSpaced xs = ignore' jsonSpaces :: xs

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

parameters {auto he  : HasBBErr s e}
           {auto pos : HasBytePos s}
           {auto pos : HasBytes s}

  export
  raise : InnerError e -> Nat -> s q => v -> F1 q v
  raise err n res = T1.do
    ps <- bytePos
    failWith (B err $ BB ps (inc n ps)) res

  export
  unexpected : List String -> s q -> F1 q (BBErr e)
  unexpected strs sk =
    read1 (error sk) >>= \case
      Just x  => pure x
      Nothing => T1.do
       bs <- read1 (bytes sk)
       ps <- bytePos
       let bnds1 := BB ps $ inc 1 ps
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
              bnds := BB ps (inc bs.size ps)
           in pure (B (Expected strs str) bnds)

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
    read1 (bytes sk) >>= \case
      BS 0 _ => unclosed s sk
      _      => unexpected ss sk

  ||| Fails with `unclosed` if this is the end of input or
  ||| a linefeed character (`\n`, byte `0x0a`) was encountered,
  ||| otherwise, invokes `unexpected`.
  export
  unclosedIfNLorEOI : String -> List String -> s q -> F1 q (BBErr e)
  unclosedIfNLorEOI s ss sk =
    read1 (bytes sk) >>= \case
      BS 0 _ => unclosed s sk
      bs     => if elem 0x0a bs then unclosed s sk else unexpected ss sk

  export %inline
  errs :
       {n : _}
    -> List (Entry n $ s q -> F1 q (BBErr e))
    -> Arr32 n (s q -> F1 q (BBErr e))
  errs = arr32 n (unexpected [])

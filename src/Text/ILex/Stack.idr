module Text.ILex.Stack

import Data.Buffer
import Data.Linear.Ref1
import Syntax.T1
import Text.ILex.Bounds
import Text.ILex.Error
import Text.ILex.Parser
import Text.ILex.Util

%hide Prelude.(>>)
%hide Prelude.(>>=)
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
  line      : s q -> Ref q Nat
  col       : s q -> Ref q Nat
  positions : s q -> Ref q (SnocList Position)

||| An interface for mutable parser stacks `s` that allow us to
||| register custom errors, which will then be raised during parsing.
public export
interface HasError (0 s : Type -> Type) (0 e : Type) | s where
  error     : s q -> Ref q (Maybe $ BoundedErr e)

||| An interface for mutable parser stacks `s` that facilitates
||| parsing string tokens containing escape sequences.
public export
interface HasStringLits (0 s : Type -> Type) where
  strings   : s q -> Ref q (SnocList String)

||| An interface for mutable parser stacks `s` that facilitates
||| parsing string tokens containing escape sequences.
public export
interface HasStack (0 s : Type -> Type) (0 a : Type) | s where
  stack     : s q -> Ref q (SnocList a)

--------------------------------------------------------------------------------
-- General Purpose Stack
--------------------------------------------------------------------------------

public export
record Stack (e,a : Type) (r : Bits32) (q : Type) where
  [search q]
  constructor S
  -- Position and token bounds
  lne      : Ref q Nat
  column   : Ref q Nat
  postns   : Ref q (SnocList Position)

  -- Custom stack type
  stck     : Ref q a

  -- Current state
  state    : Ref q (Index r)

  -- Working with string literals
  strngs  : Ref q (SnocList String)

  -- Error handling
  err     : Ref q (Maybe $ BoundedErr e)

  -- Last lexed byte string
  btes    : Ref q ByteString

export
init : (0 p : 0 < r) => a -> F1 q (Stack e a r q)
init v = T1.do
  ln <- ref1 Z
  cl <- ref1 Z
  ps <- ref1 [<]
  sk <- ref1 v
  st <- ref1 (I 0)
  ss <- ref1 [<]
  er <- ref1 Nothing
  bs <- ref1 empty
  pure (S ln cl ps sk st ss er bs)

export %inline
HasPosition (Stack e a r) where
  line      = lne
  col       = column
  positions = postns

export %inline
HasError (Stack e a r) e where
  error = err

export %inline
HasStack (Stack e (SnocList a) r) a where
  stack = stck

export %inline
HasBytes (Stack e a r) where
  bytes = btes

export %inline
HasStringLits (Stack e a r) where
  strings = strngs

--------------------------------------------------------------------------------
-- General Utilities
--------------------------------------------------------------------------------

export %inline
go : (s q => F1 q (Index r)) -> Step q r s
go f = Go $ \(x # t) => f t

export %inline
rd : HasBytes s => (s q => ByteString -> F1 q (Index r)) -> Step q r s
rd f = Rd $ \(x # t) => let bs # t := read1 (bytes x) t in f bs t

export %inline
writeAs : Ref q a -> a -> r -> F1 q r
writeAs ref v res = write1 ref v >> pure res

export %inline
push1 : Ref q (SnocList a) -> a -> F1' q
push1 ref v = T1.do
 ss <- read1 ref
 write1 ref (ss:<v)

export %inline
pop1 : Ref q (SnocList a) -> F1' q
pop1 ref =
  read1 ref >>= \case
    sv:<_ => write1 ref sv
    _     => pure ()

export %inline
replace1 : Ref q a -> a -> F1 q a
replace1 ref v = T1.do
  s <- read1 ref
  write1 ref v
  pure s

export %inline
getList : Ref q (SnocList a) -> F1 q (List a)
getList ref = T1.do
  sv <- replace1 ref [<]
  pure (sv <>> [])

--------------------------------------------------------------------------------
-- String Literals
--------------------------------------------------------------------------------

parameters {auto sk  : s q}
           {auto pos : HasStringLits s}

  export %inline
  getStr : F1 q String
  getStr = T1.do
    sv <- replace1 (strings sk) [<]
    pure $ snocPack sv

  export %inline
  pushStr : v -> String -> F1 q v
  pushStr res str = T1.do
    push1 (strings sk) str
    pure res

--------------------------------------------------------------------------------
-- Bounds and Position
--------------------------------------------------------------------------------

parameters {auto sk  : s q}
           {auto pos : HasPosition s}

  export %inline
  inccol : Nat -> F1 q ()
  inccol n = let c := col sk in read1 c >>= write1 c . (n+)

  export %inline
  incline : Nat -> F1 q ()
  incline n = T1.do
    l <- read1 (line sk)
    write1 (line sk) (n + l)
    write1 (col sk) 0

  export %inline
  getPosition : F1 q Position
  getPosition = T1.do
    l <- read1 (line sk)
    c <- read1 (col sk)
    pure $ P l c

  export %inline
  tokenBounds : Nat -> F1 q Bounds
  tokenBounds n = T1.do
    sp <- getPosition
    inccol n
    ep <- getPosition
    pure (BS sp ep)

  export %inline
  pushPosition : F1' q
  pushPosition = getPosition >>= push1 (positions sk)

  export %inline
  popPosition : F1' q
  popPosition = pop1 (positions sk)

  export %inline
  popAndGetBounds : Nat -> F1 q Bounds
  popAndGetBounds n =
    read1 (positions sk) >>= \case
      sb:<b => writeAs (positions sk) sb (BS b $ incCol n b)
      [<]   => pure Empty

  export %inline
  closeBounds : F1 q Bounds
  closeBounds = T1.do
    pe <- getPosition
    read1 (positions sk) >>= \case
      sb:<b => writeAs (positions sk) sb (BS b pe)
      [<]   => pure Empty

parameters {auto pos : HasPosition s}

  export %inline
  newline : (v : Index r) -> Step q r s
  newline v = go $ incline 1 >> pure v

  export %inline
  spaces : HasBytes s => (v : Index r) -> Step q r s
  spaces v = rd $ \bs => inccol (size bs) >> pure v

  export %inline
  jsonSpaced : HasBytes s => Index r -> Steps q r s -> Steps q r s
  jsonSpaced v xs =
    [ (plus (oneof [' ','\t']), spaces v)
    , ('\n' <|> '\r' <|> "\r\n", newline v)
    ] ++ xs

--------------------------------------------------------------------------------
-- Constant-Size Terminals
--------------------------------------------------------------------------------

public export
data ConstSize : (n : Nat) -> (x : RExp True) -> Type where
  [search x]
  CSC   : ConstSize 1 (Ch x)
  CSAnd : ConstSize m x -> ConstSize n y -> ConstSize (m+n) (And x y)
  CSOr  : ConstSize n x -> ConstSize n y -> ConstSize n (Or x y)

parameters (x          : RExp True)
           {n          : Nat}
           {auto 0 prf : ConstSize n x}
           {auto   pos : HasPosition s}

  ||| Recognizes the given character and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one *after* invoking `f`.
  export %inline
  cexpr : (s q => F1 q (Index r)) -> (RExp True, Step q r s)
  cexpr f = (x, go $ inccol n >> f)

  ||| Recognizes the given character and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one, and a new entry is pushed onto
  ||| the stack of bounds.
  export %inline
  copen : (s q => F1 q (Index r)) -> (RExp True, Step q r s)
  copen f = (x, go $ pushPosition >> inccol n >> f)

  ||| Recognizes the given character and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one, and on `Bounds` entry
  ||| is popped from the stack.
  export %inline
  cclose : (s q => F1 q (Index r)) -> (RExp True, Step q r s)
  cclose f = (x, go $ inccol n >> popPosition >> f)

--------------------------------------------------------------------------------
-- String Terminals
--------------------------------------------------------------------------------

parameters (x        : RExp True)
           {auto pos : HasPosition s}
           {auto pos : HasBytes s}

  ||| Converts the recognized token to a `String`, increases the
  ||| current column by its length and invokes the given state transformer.
  export %inline
  read : (s q => String -> F1 q (Index r)) -> (RExp True, Step q r s)
  read f =
    (x, rd $ \bs => let s := toString bs in inccol (length s) >> f s)

  ||| Converts the recognized token to a `String`, increases the
  ||| current column by its length and invokes the given state transformer.
  export %inline
  conv : (s q => ByteString -> F1 q (Index r)) -> (RExp True, Step q r s)
  conv f = (x, rd $ \bs => inccol (size bs) >> f bs)

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

parameters {auto he  : HasError s e}
           {auto pos : HasPosition s}
           {auto pos : HasBytes s}

  export
  unexpected : List String -> s q -> F1 q (BoundedErr e)
  unexpected strs sk =
    read1 (error sk) >>= \case
      Just x  => pure x
      Nothing => T1.do
       bs <- read1 (bytes sk)
       let str := toString bs
       ps <- getPosition
       let bnds := BS ps (incCol (max 1 $ length str) ps)
       case size bs of
         0 => pure (B EOI bnds)
         _ => pure (B (Expected strs str) bnds)

  export
  unclosed : String -> s q -> F1 q (BoundedErr e)
  unclosed str sk = T1.do
    bnds <- popAndGetBounds (length str)
    pure $ B (Unclosed str) bnds

  export
  unclosedIfEOI : String -> List String -> s q -> F1 q (BoundedErr e)
  unclosedIfEOI s ss sk =
    read1 (bytes sk) >>= \case
      BS 0 _ => unclosed s sk
      _      => unexpected ss sk

  export %inline
  errs :
       {n : _}
    -> List (Entry n $ s q -> F1 q (BoundedErr e))
    -> Arr32 n (s q -> F1 q (BoundedErr e))
  errs = arr32 n (unexpected [])

--------------------------------------------------------------------------------
-- Lexer
--------------------------------------------------------------------------------

parameters {0 r      : Bits32}
           {auto sk  : s q}
           {auto pos : HasPosition s}
           {auto stk : HasStack s (Bounded a)}
           {auto 0 p : 0 < r}

  export %inline
  lexPushNL : Nat -> a -> F1 q (Index r)
  lexPushNL n tok = T1.do
    bs <- tokenBounds n
    incline 1
    push1 (stack sk) (B tok bs)
    pure Ini

  export %inline
  lexPush : Nat -> a -> F1 q (Index r)
  lexPush n tok = T1.do
    bs <- tokenBounds n
    push1 (stack sk) (B tok bs)
    pure Ini

parameters (x          : RExp True)
           {auto pos   : HasPosition s}
           {auto stk   : HasStack s (Bounded a)}
           {auto 0 lt  : 0 < r}

  ||| Recognizes the given character and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one *after* invoking `f`.
  export %inline
  ctok : {n : _} -> (0 prf : ConstSize n x) => a -> (RExp True, Step q r s)
  ctok v = (x, go $ lexPush n v)

  export %inline
  readTok : HasBytes s => (String -> a) -> (RExp True, Step q r s)
  readTok f =
    (x, rd $ \bs => let s := toString bs in lexPush (length s) (f s))

  export %inline
  convTok : HasBytes s => (ByteString -> a) -> (RExp True, Step q r s)
  convTok f = (x, rd $ \bs => lexPush bs.size (f bs))

  export %inline
  nltok : HasBytes s => a -> (RExp True, Step q r s)
  nltok v = (x, rd $ \bs => lexPushNL bs.size v)

export
snocChunk : HasStack s a => s q -> F1 q (Maybe $ List a)
snocChunk sk = T1.do
  ss <- replace1 (stack sk) [<]
  pure (maybeList ss)

export
lexEOI :
     {auto 0 lt : 0 < r}
  -> {auto pos : HasPosition s}
  -> {auto stk : HasStack s a}
  -> {auto err : HasError s e}
  -> {auto bts : HasBytes s}
  -> Index r
  -> s q
  -> F1 q (Either (BoundedErr e) $ List a)
lexEOI i sk =
  if i == Ini
     then getList (stack sk) >>= pure . Right
     else unexpected [] sk >>= pure . Left

public export
0 L1 : (q,e : Type) -> Bits32 -> (a : Type) -> Type
L1 q e r a =
  P1
    q
    (BoundedErr e)
    r
    (Stack e (SnocList $ Bounded a) r)
    (List $ Bounded a)

public export
0 Lexer : (e : Type) -> Bits32 -> Type -> Type
Lexer e r a = {0 q : Type} -> L1 q e r a

export
lexer :
     {r : _}
  -> {auto 0 lt : 0 < r}
  -> Steps q r (Stack e (SnocList $ Bounded a) r)
  -> L1 q e r a
lexer m = P Ini (init [<]) (lex1 [E Ini $ dfa Err m]) snocChunk (errs []) lexEOI

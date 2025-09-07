module Text.ILex.State

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

public export
record Stack (e,a : Type) (r : Bits32) (q : Type) where
  [search q]
  constructor S
  -- Position and token bounds
  line     : Ref q Nat
  col      : Ref q Nat
  postns   : Ref q (SnocList Position)

  -- Custom stack type
  stack    : Ref q a

  -- Current state
  state    : Ref q (Index r)

  -- Working with string literals
  strings  : Ref q (SnocList String)

  -- Error handling
  error    : Ref q (Maybe $ BoundedErr e)

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
  pure (S ln cl ps sk st ss er)

--------------------------------------------------------------------------------
-- General Utilities
--------------------------------------------------------------------------------

public export
0 PStep : (e,a : Type) -> Bits32 -> Type -> Type
PStep e a r q = Step1 q (BoundedErr e) r (Stack e a r)

public export
0 PSteps : (e,a : Type) -> Bits32 -> Type -> Type
PSteps e a r q = List (RExp True, PStep e a r q)

export %inline
go : (Stack e a r q => F1 q (Index r)) -> PStep e a r q
go f = Go $ \(x # t) => f t

export %inline
rd : (Stack e a r q => ByteString -> F1 q (Index r)) -> PStep e a r q
rd f = Rd $ \(B x bs t) => f bs t

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
-- Bounds and Position
--------------------------------------------------------------------------------

parameters {auto sk : Stack e a r q}

  export %inline
  getStr : F1 q String
  getStr = T1.do
    sv <- replace1 sk.strings [<]
    pure $ snocPack sv

  export %inline
  pushStr : v -> String -> F1 q v
  pushStr res s = push1 sk.strings s >> pure res

  export %inline
  inccol : Nat -> F1 q ()
  inccol n = T1.do
    c <- read1 sk.col
    write1 sk.col (n+c)

  export %inline
  incline : Nat -> F1 q ()
  incline n = T1.do
    l <- read1 sk.line
    write1 sk.line (n + l)
    write1 sk.col 0

  export %inline
  getPosition : F1 q Position
  getPosition = T1.do
    l <- read1 sk.line
    c <- read1 sk.col
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
  pushPosition = getPosition >>= push1 sk.postns

  export %inline
  popPosition : F1' q
  popPosition = pop1 sk.postns

  export %inline
  popAndGetBounds : Nat -> F1 q Bounds
  popAndGetBounds n =
    read1 sk.postns >>= \case
      sb:<b => writeAs sk.postns sb (BS b $ {column $= (+n)} b)
      [<]   => pure Empty

export %inline
newline : (v : Index r) -> PStep e a r q
newline v = go $ incline 1 >> pure v

export %inline
spaces : (v : Index r) -> PStep e a r q
spaces v = rd $ \bs => inccol (size bs) >> pure v

export
jsonSpaced : Index r -> PSteps e a r q -> PSteps e a r q
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

  ||| Recognizes the given character and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one *after* invoking `f`.
  export %inline
  cexpr : (Stack e a r q => F1 q (Index r)) -> (RExp True, PStep e a r q)
  cexpr f = (x, go $ inccol n >> f)

  ||| Recognizes the given character and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one, and a new entry is pushed onto
  ||| the stack of bounds.
  export %inline
  copen : (Stack e a r q => F1 q (Index r)) -> (RExp True, PStep e a r q)
  copen f = cexpr $ inccol n >> pushPosition >> f

  ||| Recognizes the given character and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one, and on `Bounds` entry
  ||| is popped from the stack.
  export %inline
  cclose : (Stack e a r q => F1 q (Index r)) -> (RExp True, PStep e a r q)
  cclose f = cexpr $ inccol n >> popPosition >> f

--------------------------------------------------------------------------------
-- String Terminals
--------------------------------------------------------------------------------

||| Converts the recognized token to a `String`, increases the
||| current column by its length and invokes the given state transformer.
export %inline
read :
     RExp True
  -> (Stack e a r q => String -> F1 q (Index r))
  -> (RExp True, PStep e a r q)
read exp f =
  (exp, rd $ \bs => let s := toString bs in inccol (length s) >> f s)

||| Converts the recognized token to a `String`, increases the
||| current column by its length and invokes the given state transformer.
export %inline
conv :
     RExp True
  -> (Stack e a r q => ByteString -> F1 q (Index r))
  -> (RExp True, PStep e a r q)
conv exp f = (exp, rd $ \bs => inccol (size bs) >> f bs)

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

export
unexpected :
     List String
  -> Stack e a r q
  -> ByteString
  -> F1 q (BoundedErr e)
unexpected strs sk bs =
  read1 sk.error >>= \case
    Just x  => pure x
    Nothing => T1.do
     let str := toString bs
     ps <- getPosition
     let bnds := BS ps (incCol (max 1 $ length str) ps)
     case size bs of
       0 => pure (B EOI bnds)
       _ => pure (B (Expected strs str) bnds)

export
unclosed :
     String
  -> Stack e a r q
  -> ByteString
  -> F1 q (BoundedErr e)
unclosed s sk _ = T1.do
  bnds <- popAndGetBounds (length s)
  pure $ B (Unclosed s) bnds

export
unclosedIfEOI :
     String
  -> List String
  -> Stack e a r q
  -> ByteString
  -> F1 q (BoundedErr e)
unclosedIfEOI s ss sk bs =
  case size bs of
    0 => unclosed s sk bs
    _ => unexpected ss sk bs

export %inline
errs :
     {n : _}
  -> List (Entry n $ Stack e a r q -> ByteString -> F1 q (BoundedErr e))
  -> Arr32 n (Stack e a r q -> ByteString -> F1 q (BoundedErr e))
errs = arr32 n (unexpected [])

--------------------------------------------------------------------------------
-- Lexer
--------------------------------------------------------------------------------

public export
0 LexStack : (e,a : Type) -> Bits32 -> (q : Type) -> Type
LexStack e a = Stack e (SnocList $ Bounded a)

public export
0 LexStep : (e,a : Type) -> Bits32 -> (q : Type) -> Type
LexStep e a r q = PStep e (SnocList $ Bounded a) r q

public export
0 LexSteps : (e,a : Type) -> Bits32 -> (q : Type) -> Type
LexSteps e a r q = PSteps e (SnocList $ Bounded a) r q

parameters {auto sk  : LexStack e a r q}
           {auto 0 p : 0 < r}

  export %inline
  lexPushNL : Nat -> a -> F1 q (Index r)
  lexPushNL n tok = T1.do
    bs <- tokenBounds n
    incline 1
    push1 sk.stack (B tok bs)
    pure Ini

  export %inline
  lexPush : Nat -> a -> F1 q (Index r)
  lexPush n tok = T1.do
    bs <- tokenBounds n
    push1 sk.stack (B tok bs)
    pure Ini

parameters (x          : RExp True)
           {n          : Nat}
           {auto 0 prf : ConstSize n x}
           {auto 0 lt  : 0 < r}

  ||| Recognizes the given character and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one *after* invoking `f`.
  export %inline
  ctok : a -> (RExp True, LexStep e a r q)
  ctok v = (x, go $ lexPush n v)

export %inline
readTok :
     {auto 0 lt : 0 < r}
  -> RExp True
  -> (String -> a)
  -> (RExp True, LexStep e a r q)
readTok xp f =
  (xp, rd $ \bs => let s := toString bs in lexPush (length s) (f s))

export %inline
convTok :
     {auto 0 lt : 0 < r}
  -> RExp True
  -> (ByteString -> a)
  -> (RExp True, LexStep e a r q)
convTok xp f = (xp, rd $ \bs => lexPush bs.size (f bs))

export %inline
nltok : (0 lt : 0 < r) => RExp True -> a -> (RExp True, LexStep e a r q)
nltok xp v = (xp, rd $ \bs => lexPushNL bs.size v)

export
snocChunk : Stack e (SnocList a) r q -> F1 q (Maybe $ List a)
snocChunk sk = T1.do
  ss <- replace1 sk.stack [<]
  pure (maybeList ss)

export
lexEOI :
     {auto 0 lt : 0 < r}
  -> Index r
  -> Stack e (SnocList a) r q
  -> F1 q (Either (BoundedErr e) $ List a)
lexEOI i sk =
  if i == Ini
     then getList sk.stack >>= pure . Right
     else unexpected [] sk "" >>= pure . Left

public export
0 L1 : (q,e : Type) -> Bits32 -> (a : Type) -> Type
L1 q e r a = P1 q (BoundedErr e) r (LexStack e a r) (List $ Bounded a)

public export
0 Lexer : (e : Type) -> Bits32 -> Type -> Type
Lexer e r a = {0 q : Type} -> L1 q e r a

export
lexer : {r : _} -> (0 lt : 0 < r) => LexSteps e a r q -> L1 q e r a
lexer m = P Ini (init [<]) (lex1 [E Ini $ dfa Err m]) snocChunk (errs []) lexEOI

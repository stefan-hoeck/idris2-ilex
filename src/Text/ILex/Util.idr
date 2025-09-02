module Text.ILex.Util

import Data.ByteString
import Data.Linear.Ref1
import Derive.Prelude
import Syntax.T1
import Text.ILex.Bounds
import Text.ILex.Error
import Text.ILex.Parser
import Text.ILex.RExp

%hide Prelude.(>>=)
%hide Prelude.(>>)
%default total

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
  bounds : s q -> Ref q (SnocList Bounds)

export %inline
go : (s q -> F1 q (Index r)) -> Step1 q e r s
go f = Go $ \(x # t) => f x t

export %inline
rd : (s q -> ByteString -> F1 q (Index r)) -> Step1 q e r s
rd f = Rd $ \(B x bs t) => f x bs t

export %inline
prs : (s q -> ByteString -> F1 q (Either e (Index r))) -> Step1 q e r s
prs f = Prs $ \(B x bs t) => f x bs t

public export
interface LC s => LexST s a | s where
  vals : s q -> Ref q (SnocList $ Bounded a)

||| A record of mutable variables that can be used for
||| basic lexing tasks
public export
record LexState a q where
  constructor LS
  line : Ref q Nat
  col  : Ref q Nat
  bnds : Ref q (SnocList Bounds)
  vals : Ref q (SnocList a)

export %inline
LC (LexState a) where
  line   = LexState.line
  col    = LexState.col
  bounds = LexState.bnds

export %inline
LexST (LexState (Bounded a)) a where
  vals = LexState.vals

export
init : F1 q (LexState a q)
init = T1.do
  l <- ref1 Z
  c <- ref1 Z
  b <- ref1 [<]
  v <- ref1 [<]
  pure (LS l c b v)

--------------------------------------------------------------------------------
-- General Utilities
--------------------------------------------------------------------------------

export %inline
writeAs : Ref q a -> a -> r -> F1 q r
writeAs ref v res = write1 ref v >> pure res

export %inline
push1 : Ref q (SnocList a) -> r -> a -> F1 q r
push1 ref res v = T1.do
 ss <- read1 ref
 writeAs ref (ss:<v) res

export %inline
push :
     (0 s : Type -> Type)
  -> (s q -> Ref q (SnocList a))
  -> r
  -> a
  -> s q
  -> F1 q r
push _ f tgt v stck t = push1 (f stck) tgt v t

export %inline
const : (0 s : Type -> Type) -> r -> s q -> F1 q r
const _ v _ t = v # t

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

export %inline
getStr : Ref q (SnocList String) -> F1 q String
getStr ref = T1.do
  sv <- replace1 ref [<]
  pure $ snocPack sv

export %inline
state : RExp True -> Index r -> (RExp True, Step1 q e r s)
state exp v = (exp, go $ \_,t => v # t)

--------------------------------------------------------------------------------
-- Handling positions
--------------------------------------------------------------------------------

parameters {0 q : Type}
           {0 s : Type -> Type}
           {auto lc : LC s}

  export %inline
  incCols : Nat -> s q -> r -> F1 q r
  incCols n x v = T1.do
    c <- read1 (col x)
    writeAs (col x) (c+n) v

  export %inline
  incLine : t -> s q -> F1 q t
  incLine v x = T1.do
    l <- read1 (line x)
    write1 (line x) (S l)
    write1 (col x) 0
    pure v

  export %inline
  newline : (v : Index k) -> Step1 q e k s
  newline v = go $ incLine v

  export %inline
  spaces : (v : Index k) -> Step1 q e k s
  spaces v = rd $ \x,bs => incCols (size bs) x v

  export
  jsonSpaced : Index k -> TokenMap (Step1 q e k s) -> TokenMap (Step1 q e k s)
  jsonSpaced v xs =
    [ (plus (oneof [' ','\t']), spaces v)
    , ('\n' <|> '\r' <|> "\r\n", newline v)
    ] ++ xs

--------------------------------------------------------------------------------
-- Bounds
--------------------------------------------------------------------------------

  export %inline
  currentPos : s q -> F1 q Position
  currentPos x = T1.do
    l <- read1 (line x)
    c <- read1 (col x)
    pure $ P l c

  export %inline
  popBounds : s q -> F1 q Bounds
  popBounds x =
    read1 (bounds x) >>= \case
      sb:<b => writeAs (bounds x) sb b
      [<]   => pure Empty

  export %inline
  incColAndGetBounds : Nat -> s q -> F1 q Bounds
  incColAndGetBounds n x = T1.do
    l <- read1 (line x)
    c <- read1 (col x)
    let d := c + n
    write1 (col x) d
    pure $ BS (P l c) (P l $ pred d)

  export %inline
  incLineAndGetBounds : Nat -> s q -> F1 q Bounds
  incLineAndGetBounds n x = T1.do
    l <- read1 (line x)
    c <- read1 (col x)
    let d := c + n
    write1 (col x) 0
    write1 (line x) (S l)
    pure $ BS (P l c) (P l $ pred d)

  export %inline
  pushPos : s q -> F1' q
  pushPos x = T1.do
    l  <- read1 (line x)
    c  <- read1 (col x)
    write1 (col x) (S c)
    let p := P l c
    push1 (bounds x) () (BS p p)

  ||| Recognizes the given character and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one, and a new entry is pushed onto
  ||| the stack of bounds.
  export %inline
  copen : Char -> (s q -> F1 q (Index r)) -> (RExp True, Step1 q e r s)
  copen c f = (chr c, go $ \p => pushPos p >> f p)

  ||| Recognizes the given character and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one, and on `Bounds` entry
  ||| is popped from the stack.
  export %inline
  cclose : Char -> (s q -> F1 q (Index r)) -> (RExp True, Step1 q e r s)
  cclose c f = (chr c, go $ \p => popBounds p >>= \_ => f p >>= incCols 1 p)

--------------------------------------------------------------------------------
-- Terminals
--------------------------------------------------------------------------------

  ||| Recognizes the given string and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by the length of `v` *after* invoking `f`.
  export %inline
  str :
       (v : String)
    -> {auto 0 prf : NonEmpty (unpack v)}
    -> (f : s q -> F1 q (Index r))
    -> (RExp True, Step1 q e r s)
  str v f =
   let len := length v
    in (str v, go $ \p => f p >>= incCols len p)

  ||| Recognizes the given character and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one *after* invoking `f`.
  export %inline
  chr : Char -> (s q -> F1 q (Index r)) -> (RExp True, Step1 q e r s)
  chr c f = (chr c, go $ \p => f p >>= incCols 1 p)

  ||| Like `chr` but returns the given result directly.
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one as with `chr`.
  export %inline
  chr' : Char -> Index r -> (RExp True, Step1 q e r s)
  chr' c v = chr c $ \_ => pure v

  ||| Converts the recognized token to a `String`, increases the
  ||| current column by its length and invokes the given state transformer.
  export %inline
  read :
       RExp True
    -> (String -> s q -> F1 q (Index r))
    -> (RExp True, Step1 q e r s)
  read exp f =
    ( exp
    , rd $ \st,bs => T1.do
        let s     := toString bs
        f s st >>= incCols (length s) st
    )

  ||| Increases the current column by the recognized byte string's length
  ||| before passing it on to the given state transformer.
  export %inline
  conv :
       RExp True
    -> (ByteString -> s q -> F1 q (Index r))
    -> (RExp True, Step1 q e r s)
  conv exp f = (exp, rd $ \st,bs => f bs st >>= incCols (size bs) st)

  ||| Like `read` put for transitions that ignore the token's
  ||| byte sequence.
  |||
  ||| Note: Consider using `str` or `chr` if the recognized byte sequence
  |||       is a constant.
  export %inline
  read' : RExp True -> (s q -> F1 q (Index r)) -> (RExp True, Step1 q e r s)
  read' exp f = read exp (const f)

  ||| Like `conv` put for transitions that ignore the token's
  ||| byte sequence.
  |||
  ||| Note: Consider using `str` or `chr` if the recognized byte sequence
  |||       is a constant.
  export %inline
  conv' : RExp True -> (s q -> F1 q (Index r)) -> (RExp True, Step1 q e r s)
  conv' exp f = conv exp (const f)

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

  export
  unexpected : List String -> s q -> ByteString -> F1 q (BoundedErr e)
  unexpected strs st bs t =
   let str     := toString bs
       cur # t := currentPos st t
       end     := {column $= (+ (pred $ length str))} cur
    in case size bs of
         0 => B EOI (BS cur end) # t
         _ => B (Expected strs str) (BS cur end) # t

  export
  unclosed : String -> s q -> ByteString -> F1 q (BoundedErr e)
  unclosed s st bs t =
   let p # t := popBounds st t
    in B (Unclosed s) p # t

  export
  unclosedIfEOI : String -> List String -> s q -> ByteString -> F1 q (BoundedErr e)
  unclosedIfEOI s ss st bs =
    case size bs of
      0 => unclosed s st bs
      _ => unexpected ss st bs

  export %inline
  errs :
       {n : _}
    -> List (Entry n $ s q -> ByteString -> F1 q (BoundedErr e))
    -> Arr32 n ( s q -> ByteString -> F1 q (BoundedErr e))
  errs = arr32 n (unexpected [])

--------------------------------------------------------------------------------
-- Lexer
--------------------------------------------------------------------------------

parameters {0 s       : Type -> Type}
           {0 a,q     : Type}
           {auto lst  : LexST s a}

  export %inline
  lexPushNL : Nat -> r -> a -> s q -> F1 q r
  lexPushNL n res v x = T1.do
    bs <- incLineAndGetBounds n x
    push1 (vals x) res (B v bs)

  export %inline
  lexPush : Nat -> r -> a -> s q -> F1 q r
  lexPush n res v x = T1.do
    bs <- incColAndGetBounds n x
    push1 (vals x) res (B v bs)

  export %inline
  ctok : (0 lt : 0 < r) => Char -> a -> (RExp True, Step1 q e r s)
  ctok c res = (chr c, go $ lexPush 1 Ini res)

  export %inline
  stok :
       {auto 0 lt : 0 < r}
    -> (str : String)
    -> {auto 0 p : NonEmpty (unpack str)}
    -> a
    -> (RExp True, Step1 q e r s)
  stok s res = (str s, go $ lexPush (length s) Ini res)

  export %inline
  readTok :
       {auto 0 lt : 0 < r}
    -> RExp True
    -> (String -> a)
    -> (RExp True, Step1 q e r s)
  readTok xp f =
    (xp, rd $ \x,bs => let s := toString bs in lexPush (length s) Ini (f s) x)

  export %inline
  convTok :
       {auto 0 lt : 0 < r}
    -> RExp True
    -> (ByteString -> a)
    -> (RExp True, Step1 q e r s)
  convTok xp f = (xp, rd $ \x,bs => lexPush bs.size Ini (f bs) x)

  export %inline
  nltok : (0 lt : 0 < r) => RExp True -> a -> (RExp True, Step1 q e r s)
  nltok xp v = (xp, rd $ \x,bs => lexPushNL bs.size Ini v x)

export
snocChunk :
     (0 s : Type -> Type)
  -> (s q -> Ref q (SnocList a))
  -> s q
  -> F1 q (Maybe $ List a)
snocChunk s f x t = let ss # t := replace1 (f x) [<] t in maybeList ss # t

export
lchunk : LexST s a => s q -> F1 q (Maybe $ List $ Bounded a)
lchunk s t = let ss # t := replace1 (vals s) [<] t in maybeList ss # t

leoi : Index 1 -> LexState a q -> F1 q (Either e $ List a)
leoi _ s = replace1 s.vals [<] >>= pure . Right . (<>> [])

public export
0 L1 : (q,e,a : Type) -> Type
L1 q e a = P1 q (BoundedErr e) 1 (LexState $ Bounded a) (List $ Bounded a)

public export
0 Lexer : (e,a : Type) -> Type
Lexer e a = {0 q : Type} -> L1 q e a

export
lexer : TokenMap (Step1 q (BoundedErr e) 1 (LexState $ Bounded a)) -> L1 q e a
lexer m = P Ini init (lex1 [E Ini $ dfa Err m]) lchunk (errs []) leoi

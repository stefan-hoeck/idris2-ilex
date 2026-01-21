module Text.ILex.Stack

import Data.Linear.Ref1
import Syntax.T1
import Text.Bounds
import Text.ILex.Derive
import Text.ILex.Interfaces
import Text.ILex.Parser
import Text.ILex.Util
import Text.ParseError

%hide Prelude.(>>)
%hide Prelude.(>>=)
%hide Prelude.pure
%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- General Purpose Stack
--------------------------------------------------------------------------------

||| A general-purpose mutable parser stack that can be used in many common
||| situation, such as when needing just a lexer or wanting to parse
||| a single value of a simple type.
|||
||| For concrete usage examples, see ilex-json and ilex-toml, which both
||| make use of this type as their mutable parser state.
|||
||| If you are writing a parser for something complex such as a programming
||| language, you're probably going to need quite a few custom fields, so
||| feel free to come up with your own.
public export
record Stack (e,a : Type) (r : Bits32) (q : Type) where
  [search q]
  constructor S
  -- Position and token bounds
  line_      : Ref q Nat
  col_       : Ref q Nat
  positions_ : Ref q (SnocList Position)

  -- Custom stack type
  stack_     : Ref q a

  -- Current state
  state_     : Ref q (Index r)

  -- Working with string literals
  strings_   : Ref q (SnocList String)

  -- Error handling
  error_     : Ref q (Maybe $ BoundedErr e)

  -- Last lexed byte string
  bytes_     : Ref q ByteString

%runElab derive "Stack" [FullStack]

||| Initializes a new parser stack.
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

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------

%runElab deriveParserState "VSz" "VST" ["VIni", "VErr", "VDone"]

||| Description of lexicographic tokens
|||
||| These are used to convert a lexer state to a token (or an error)
||| of the appropriate type. Every lexer state corresponds to exactly
||| one convertion. Typically, most lexer states are non-terminal
||| states, so they correspond to `Bottom`.
public export
data Tok : (e, a : Type) -> Type where
  ||| Marks a terminal state that does not produce a token.
  ||| This can be used for comments or whitespace that should be
  ||| ignored.
  Ignore : Tok e a

  ||| A constant token that allows us to emit a value directly.
  Const  : a -> Tok e a

  ||| A token that needs to be parsed from its corresponding bytestring.
  Txt    : (String -> Either e a) -> Tok e a

  ||| A token that needs to be parsed from its corresponding bytestring.
  Bytes  : (ByteString -> Either e a) -> Tok e a

export %inline
const : a -> Tok e a
const = Const

export %inline
txt : (String -> a) -> Tok e a
txt f = Txt (Right . f)

export %inline
bytes : (ByteString -> a) -> Tok e a
bytes f = Bytes (Right . f)

toStep :
     (RExpOf True b, Tok e a)
  -> (RExpOf True b, Step q VSz (Stack e (Maybe a) VSz))
toStep (x,c) =
  case c of
    Ignore  => conv' x VIni
    Const v => conv x (\_ => putStackAs (Just v) VDone)
    Txt f   =>
      read x $ \s => case f s of
        Right v => putStackAs (Just v) VDone
        Left e  => failHere (Custom e) VErr
    Bytes f =>
      conv x $ \s => case f s of
        Right v => putStackAs (Just v) VDone
        Left e  => failHere (Custom e) VErr

ignore :
     (RExpOf True b, Tok e a)
  -> Maybe (RExpOf True b, Step q VSz (Stack e (Maybe a) VSz))
ignore (x,Ignore) = Just $ conv' x VDone
ignore _          = Nothing

valEOI : VST -> Stack e (Maybe a) VSz q -> F1 q (Either (BoundedErr e) a)
valEOI i sk =
  if i == VDone || i == VIni
     then replace1 sk.stack_ Nothing >>= \case
            Just v  => pure (Right v)
            Nothing => unexpected [] sk >>= pure . Left
     else unexpected [] sk >>= pure . Left

public export
0 PVal1 : (q,e : Type) -> (a : Type) -> Type
PVal1 q e a = P1 q (BoundedErr e) VSz (Stack e (Maybe a) VSz) a

||| Parser for simple values based on regular expressions.
export
value : Maybe a -> TokenMap (Tok e a) -> PVal1 q e a
value mv m =
 let iniSteps  := E VIni $ dfa (map toStep m)
     doneSteps := E VDone $ dfa (mapMaybe ignore m)
     states    := lex1 [iniSteps, doneSteps]
  in P VIni (init mv) states noChunk (errs []) valEOI

--------------------------------------------------------------------------------
-- Lexer
--------------------------------------------------------------------------------

parameters {0 r      : Bits32}
           {auto sk  : s q}
           {auto pos : HasPosition s}
           {auto stk : HasStack s (SnocList $ Bounded a)}
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

parameters (x          : RExpOf True b)
           {auto pos   : HasPosition s}
           {auto stk   : HasStack s (SnocList $ Bounded a)}
           {auto 0 lt  : 0 < r}

  ||| Recognizes the given character and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one *after* invoking `f`.
  export %inline
  ctok : {n : _} -> (0 prf : ConstSize n x) => a -> (RExpOf True b, Step q r s)
  ctok v = go x $ lexPush n v

  export %inline
  readTok : HasBytes s => (String -> a) -> (RExpOf True b, Step q r s)
  readTok f = goStr x $ \s => lexPush (length s) (f s)

  export %inline
  convTok : HasBytes s => (ByteString -> a) -> (RExpOf True b, Step q r s)
  convTok f = goBS x $ \bs => lexPush bs.size (f bs)

  export %inline
  nltok : HasBytes s => a -> (RExpOf True b, Step q r s)
  nltok v = goBS x $ \bs => lexPushNL bs.size v

export
lexEOI :
     {auto 0 lt : 0 < r}
  -> {auto pos : HasPosition s}
  -> {auto stk : HasStack s (SnocList a)}
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
  -> {auto 0 lt  : 0 < r}
  -> Steps q r (Stack e (SnocList $ Bounded a) r)
  -> L1 q e r a
lexer m =
  P Ini (init [<]) (lex1 [E Ini $ dfa m]) snocChunk (errs []) lexEOI

module Text.ILex.Stack

import Data.Linear.Ref1
import Syntax.T1
import Text.ByteBounds
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
  bufSize_    : Nat
  prev_       : ByteString
  cur_        : IBuffer bufSize_
  prevOffset_ : Nat
  curOffset_  : Nat
  from_       : Ref q (LTENat bufSize_)
  till_       : Ref q (LTENat bufSize_)
  positions_  : Ref q (SnocList BytePos)

  -- Custom stack type
  stack_     : Ref q a

  -- Current state
  state_     : Ref q (Index r)

  -- Working with string literals
  strings_   : Ref q (SnocList String)

  -- Error handling
  error_     : Ref q (Maybe $ BBErr e)

%runElab derive "Stack" [FullStack]

||| Initializes a new parser stack.
export
init : (0 p : 0 < r) => a -> (n : Nat) -> IBuffer n -> F1 q (Stack e a r q)
init v n buf = T1.do
  rf <- ref1 (first n)
  rt <- ref1 (first n)
  ps <- ref1 [<]
  sk <- ref1 v
  st <- ref1 (I 0)
  ss <- ref1 [<]
  er <- ref1 Nothing
  pure (S n empty buf 0 0 rf rt ps sk st ss er)

--------------------------------------------------------------------------------
-- Lexer
--------------------------------------------------------------------------------

public export
0 Tok : Type -> Type
Tok = ByteBounded

public export
0 Toks : Type -> Type
Toks = List . Tok

public export
0 Skot : Type -> Type
Skot = SnocList . ByteBounded

public export
0 L1 : (q,e : Type) -> (a : Type) -> Type
L1 q e a = P1 q (BBErr e) (Toks a)

public export
0 Lexer : (e : Type) -> Type -> Type
Lexer e a = {0 q : Type} -> L1 q e a

parameters {auto hb   : HasBytes s}
           {auto hs   : HasStack s (Skot a)}
           (x         : RExp True)
           {auto 0 lt : 0 < r}

  export %inline
  pushBounded : s q => a -> F1 q (Index r)
  pushBounded v = bounded' v >>= \b => pushStackAs b 0

  export %inline
  tok : a -> (RExp True, Step q r s)
  tok v = step x (pushBounded v)

  export %inline
  byteTok : (ByteString -> a) -> (RExp True, Step q r s)
  byteTok f = bytes x (pushBounded . f)

  export %inline
  stringTok : (String -> a) -> (RExp True, Step q r s)
  stringTok f = string x (pushBounded . f)

export
lexEOI :
     {auto 0 lt : 0 < r}
  -> {auto stk : HasStack s (SnocList a)}
  -> {auto err : HasBBErr s e}
  -> {auto bts : HasBytes s}
  -> Index r
  -> s q
  -> F1 q (Either (BBErr e) $ List a)
lexEOI i sk =
  if i == Ini
     then getList (stack sk) >>= pure . Right
     else unexpected [] sk >>= pure . Left

export
lexer : {r : _} -> (0 lt : 0 < r) => Steps q r (Stack e (Skot a) r) -> L1 q e a
lexer m = P Ini (init [<]) (lex1 [E Ini $ dfa m]) snocChunk (errs []) lexEOI

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------

%runElab deriveParserState "VSz" "VST" ["VIni", "VErr", "VDone"]

||| Description of lexicographic tokens
public export
data Token : (e, a : Type) -> Type where
  ||| Marks a terminal state that does not produce a token.
  ||| This can be used for comments or whitespace that should be
  ||| ignored.
  Ignore : Token e a

  ||| A constant token that allows us to emit a value directly.
  Const  : a -> Token e a

  ||| A token that needs to be parsed from its corresponding bytestring.
  Txt    : (String -> Either e a) -> Token e a

  ||| A token that needs to be parsed from its corresponding bytestring.
  Bytes  : (ByteString -> Either e a) -> Token e a

export %inline
const : a -> Token e a
const = Const

export %inline
txt : (String -> a) -> Token e a
txt f = Txt (Right . f)

export %inline
bytes : (ByteString -> a) -> Token e a
bytes f = Bytes (Right . f)

toStep :
     (RExpOf True b, Token e a)
  -> (RExpOf True b, Step q VSz (Stack e (Maybe a) VSz))
toStep (x,c) =
  case c of
    Ignore  => step' x VIni
    Const v => step x (putStackAs (Just v) VDone)
    Txt f   =>
      string x $ \s => case f s of
        Right v => putStackAs (Just v) VDone
        Left e  => failHere (Custom e) VErr
    Bytes f =>
      bytes x $ \s => case f s of
        Right v => putStackAs (Just v) VDone
        Left e  => failHere (Custom e) VErr

ignore :
     (RExpOf True b, Token e a)
  -> Maybe (RExpOf True b, Step q VSz (Stack e (Maybe a) VSz))
ignore (x,Ignore) = Just $ step' x VDone
ignore _          = Nothing

valEOI : VST -> Stack e (Maybe a) VSz q -> F1 q (Either (BBErr e) a)
valEOI i sk =
  if i == VDone || i == VIni
     then replace1 sk.stack_ Nothing >>= \case
            Just v  => pure (Right v)
            Nothing => unexpected [] sk >>= pure . Left
     else unexpected [] sk >>= pure . Left

public export
0 PVal1 : (q,e : Type) -> (a : Type) -> Type
PVal1 q e a = P1 q (BBErr e) a

||| Parser for simple values based on regular expressions.
export
value : Maybe a -> TokenMap (Token e a) -> PVal1 q e a
value mv m =
 let iniSteps  := E VIni $ dfa (map toStep m)
     doneSteps := E VDone $ dfa (mapMaybe ignore m)
     states    := lex1 [iniSteps, doneSteps]
  in P VIni (init mv) states noChunk (errs []) valEOI

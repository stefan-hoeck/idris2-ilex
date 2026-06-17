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
  prev_      : Ref q (Maybe ByteString)
  full_      : Ref q ByteString
  pos_       : Ref q BytePos
  len_       : Ref q Nat
  positions_ : Ref q (SnocList BytePos)

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
init : (0 p : 0 < r) => a -> F1 q (Stack e a r q)
init v = T1.do
  pr <- ref1 Nothing
  fl <- ref1 empty
  bp <- ref1 (BP Z)
  ll <- ref1 Z
  ps <- ref1 [<]
  sk <- ref1 v
  st <- ref1 (I 0)
  ss <- ref1 [<]
  er <- ref1 Nothing
  pure (S pr fl bp ll ps sk st ss er)

--------------------------------------------------------------------------------
-- Lexer
--------------------------------------------------------------------------------

parameters {auto hb   : HasBytes s}
           {auto hs   : HasStack s (SnocList $ ByteBounded a)}
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
  -> {auto pos : HasBytePos s}
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

public export
0 L1 : (q,e : Type) -> (a : Type) -> Type
L1 q e a = P1 q (BBErr e) (List $ ByteBounded a)

public export
0 Lexer : (e : Type) -> Type -> Type
Lexer e a = {0 q : Type} -> L1 q e a

export
lexer :
     {r : _}
  -> {auto 0 lt  : 0 < r}
  -> Steps q r (Stack e (SnocList $ ByteBounded a) r)
  -> L1 q e a
lexer m =
  P Ini (init [<]) (lex1 [E Ini $ dfa m]) snocChunk (errs []) lexEOI

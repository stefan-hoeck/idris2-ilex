module Text.ILex.Stack

import Data.Linear.Ref1
import Syntax.T1
import Text.ILex.Bounds
import Text.ILex.Derive
import Text.ILex.Error
import Text.ILex.Interfaces
import Text.ILex.Parser
import Text.ILex.Util

%hide Prelude.(>>)
%hide Prelude.(>>=)
%hide Prelude.pure
%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- General Purpose Stack
--------------------------------------------------------------------------------

%logging "derive.claims" 1
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

parameters (x          : RExp True)
           {auto pos   : HasPosition s}
           {auto stk   : HasStack s (SnocList $ Bounded a)}
           {auto 0 lt  : 0 < r}

  ||| Recognizes the given character and uses it to update the parser state
  ||| as specified by `f`.
  |||
  ||| The current column is increased by one *after* invoking `f`.
  export %inline
  ctok : {n : _} -> (0 prf : ConstSize n x) => a -> (RExp True, Step q r s)
  ctok v = go x $ lexPush n v

  export %inline
  readTok : HasBytes s => (String -> a) -> (RExp True, Step q r s)
  readTok f = goStr x $ \s => lexPush (length s) (f s)

  export %inline
  convTok : HasBytes s => (ByteString -> a) -> (RExp True, Step q r s)
  convTok f = goBS x $ \bs => lexPush bs.size (f bs)

  export %inline
  nltok : HasBytes s => a -> (RExp True, Step q r s)
  nltok v = goBS x $ \bs => lexPushNL bs.size v

export
snocChunk : HasStack s (SnocList a) => s q -> F1 q (Maybe $ List a)
snocChunk sk = T1.do
  ss <- replace1 (stack sk) [<]
  pure (maybeList ss)

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

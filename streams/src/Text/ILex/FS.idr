module Text.ILex.FS

import public FS
import public Text.ILex

import Derive.Prelude

%default total
%language ElabReflection

||| Lexing state.
|||
||| This encapsulates the current state as well as
||| the remainder of the previous chunk that marks
||| the beginning of the current token.
public export
record SLexState (n : Nat) where
  constructor LST
  line : Nat
  col  : Nat
  cur  : Fin (S n)
  prev : ByteString

%runElab deriveIndexed "SLexState" [Show]

||| Result of a partial lexing step: In such a step, we lex
||| till the end of a chunk of bytes, allowing for a remainder of
||| bytes that could not yet be identified as a tokens.
public export
data SLexRes : (n : Nat) -> Type -> Type -> Type where
  Err  : Bounds -> InnerError a e -> SLexRes n e a
  Toks : SLexState n -> SnocList (Bounded a) -> SLexRes n e a

%runElab derivePattern "SLexRes" [I,P,P] [Show]

||| Operates a lexer on a chunk of bytes
||| starting from the given lexer state.
export
lexChunk :
     Origin
  -> (l : Lexer e a)
  -> SLexState l.states
  -> (n ** IBuffer n)
  -> SLexRes l.states e a

parameters {0 e,a    : Type}
           {0 states : Nat}
           {0 n      : Nat}
           (next     : Stepper states)
           (term     : IArray (S states) (Maybe $ Conv e a))
           (buf      : IBuffer n)

  covering
  inner :
       (start       : Nat)                  -- start of current token
    -> (vals        : SnocList $ Bounded a) -- accumulated tokens
    -> (pos         : Nat)                  -- reverse position in the byte array
    -> {auto x      : Ix pos n}             -- position in the byte array
    -> {auto 0 lte2 : LTE start (ixToNat x)}
    -> (cur         : Fin (S states))       -- current automaton state
    -> SLexRes states e a

  -- -- Accumulates lexemes by applying the maximum munch strategy:
  -- -- The largest matched lexeme is consumed and kept.
  -- covering
  -- loop :
  --      (vals   : SnocList $ Bounded a) -- accumulated tokens
  --   -> (pos    : Nat)                  -- reverse position in the byte array
  --   -> {auto x : Ix pos n}             -- position in the byte array
  --   -> PLexRes states e a
  -- loop vals 0     = Toks (LST 0 empty) vals
  -- loop vals (S k) =
  --   case (next `at` 0) `atByte` (buf `ix` k) of
  --     0 => Err (atPos $ ixToNat x) (Byte $ buf `ix` k)
  --     s => inner (term `at` s) (ixToNat x) k vals k s

  -- app :
  --      SnocList (Bounded a)
  --   -> Conv e a
  --   -> (from        : Nat)
  --   -> (till        : Nat)
  --   -> {auto ix     : Ix (S till) n}
  --   -> {auto 0  lte : LTE from (ixToNat ix)}
  --   -> PLexRes states e a
  -- app sx c from till =
  --   let bs := BS from (ixToNat ix)
  --    in case c of
  --         Const v => loop (sx :< B v bs) till
  --         Ignore  => loop sx till
  --         Err   x => Err bs (Custom x)
  --         Txt   f => case f (toByteString buf from till) of
  --           Left  x => Err bs (Custom x)
  --           Right v => loop (sx :< B v bs) till

  -- inner start vals 0     cur =
  --   case last of
  --     Nothing => Toks (LST cur (toByteString buf start lastPos)) vals
  --     Just i  => app vals i start lastPos
  -- inner last start lastPos vals (S k) cur =
  --   let arr  := next `at` cur
  --       byte := ix buf k
  --    in case arr `atByte` byte of
  --         FZ => case last of
  --           Nothing => Err (atPos $ ixToNat x) (Byte $ buf `ix` k)
  --           Just i  => app vals i start lastPos
  --         x  => case term `at` x of
  --           Nothing => inner last     start lastPos vals k x
  --           Just i  => inner (Just i) start k       vals k x

-- plexFrom (L ss nxt t _) pos buf = assert_total $ loop nxt t buf [<] pos

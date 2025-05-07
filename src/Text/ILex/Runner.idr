module Text.ILex.Runner

import public Data.ByteString
import public Data.Linear.Token
import public Data.Vect
import public Text.ILex.Lexer

import Data.Buffer
import Data.Buffer.Core
import Data.Buffer.Indexed
import Derive.Prelude

%default total
%language ElabReflection

||| Lexing state.
|||
||| This encapsulates the current state as well as
||| the remainder of the previous chunk that marks
||| the beginning of the current token.
public export
record LexState (n : Nat) where
  constructor LST
  cur  : Fin (S n)
  prev : ByteString

%runElab deriveIndexed "LexState" [Show]

export
init : LexState n
init = LST 0 empty

public export
data LexRes : (n : Nat) -> Type -> Type where
  EOI  : Nat -> LexRes n a
  Err  : Nat -> Bits8 -> LexRes n a
  Toks : LexState n -> List a -> LexRes n a

%runElab derivePattern "LexRes" [I,P] [Show]

lexFrom :
     (l : Lexer a)
  -> LexState l.states
  -> (pos : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> LexRes l.states a

||| Operates a lexer on a chunk of bytes returning
||| starting from the given lexer state.
|||
||| This is the most general form, allowing us to
||| begin and stop in the middle of a token, which
||| is important for streaming.
export %inline
lexChunk :
     (l : Lexer a)
  -> LexState l.states
  -> (n ** IBuffer n)
  -> LexRes l.states a
lexChunk l s (n ** buf) = lexFrom l s n buf

||| Like `lexChunk` but processes data from a single buffer.
export %inline
lex : {n : _} -> (l : Lexer a) -> IBuffer n -> LexRes l.states a
lex l buf = lexChunk l init (n ** buf)

||| Like `lexChunk` but processes data from a single buffer.
export
lexString : (l : Lexer a) -> String -> LexRes l.states a
lexString l s = lex l (fromString s)

offsetToIx : (o : Nat) -> Ix s (o+s)
offsetToIx 0     = IZ
offsetToIx (S k) = rewrite plusSuccRightSucc k s in IS (offsetToIx k)

||| Like `lexChunk` but processes data from a single byte string.
export %inline
lexBytes : (l : Lexer a) -> ByteString -> LexRes l.states a
lexBytes l (BS s $ BV buf o lte) =
  lexFrom l init s {x = offsetToIx o} (take (o+s) buf)

--------------------------------------------------------------------------------
-- Lexer run loop
--------------------------------------------------------------------------------

toByteString :
     ByteString
  -> IBuffer n
  -> (from        : Nat)
  -> (0    till   : Nat)
  -> {auto ix     : Ix (S till) n}
  -> {auto 0  lte : LTE from (ixToNat ix)}
  -> ByteString
toByteString prev buf from till =
  let bv := fromIBuffer buf
   in prev <+> (BS _ $ substringFromTo from (ixToNat ix) {lt = ixLT ix} bv)

app :
     {0 n : _}
  -> ByteString
  -> SnocList a
  -> Conv a
  -> IBuffer n
  -> (from        : Nat)
  -> (0    till   : Nat)
  -> {auto ix     : Ix (S till) n}
  -> {auto 0  lte : LTE from (ixToNat ix)}
  -> SnocList a
app prev sx (Const val) buf from till = sx :< val
app prev sx (Txt f)     buf from till = sx :< f (toByteString prev buf from till)
app prev sx _           buf from till = sx

parameters {0 a      : Type}
           {0 states : Nat}
           {0 n      : Nat}
           (next     : IArray (S states) (IArray 256 (Fin (S states))))
           (term     : IArray (S states) (Maybe $ Conv a))
           (buf      : IBuffer n)

  covering
  inner :
       (prev        : ByteString)
    -> (last        : Maybe $ Conv a)   -- last encountered terminal state
    -> (start       : Nat)              -- start of current token
    -> (lastPos     : Nat)              -- counter for last byte in `last`
    -> {auto y      : Ix (S lastPos) n} -- end position in the byte array of `last`
    -> (vals        : SnocList a)       -- accumulated tokens
    -> (pos         : Nat)              -- reverse position in the byte array
    -> {auto x      : Ix pos n}         -- position in the byte array
    -> {auto 0 lte1 : LTE start (ixToNat y)}
    -> {auto 0 lte2 : LTE start (ixToNat x)}
    -> (cur         : Fin (S states))   -- current automaton state
    -> LexRes states a

  -- Accumulates lexemes by applying the maximum munch strategy:
  -- The largest matched lexeme is consumed and kept.
  covering
  loop :
       (prev    : ByteString)       -- beginning of current token
    -> (vals    : SnocList a)       -- accumulated tokens
    -> (pos     : Nat)              -- reverse position in the byte array
    -> (cur     : Fin (S states))
    -> {auto x  : Ix pos n}         -- position in the byte array
    -> LexRes states a
  loop prev vals 0     cur = Toks (LST cur prev) (vals <>> [])
  loop prev vals (S k) cur =
    case (next `at` cur) `atByte` (buf `ix` k) of
      0 => Err (ixToNat x) (buf `ix` k)
      s => inner prev (term `at` s) (ixToNat x) k vals k s

  inner prev last start lastPos vals 0     cur =
    case last of
      Nothing => Toks (LST cur (toByteString prev buf start lastPos)) (vals <>> [])
      Just i  => loop empty (app prev vals i buf start lastPos) lastPos 0
  inner prev last start lastPos vals (S k) cur =
    let arr  := next `at` cur
        byte := ix buf k
     in case arr `atByte` byte of
          FZ => case last of
            Nothing => Err (ixToNat x) (buf `ix` k)
            Just i  => loop empty (app prev vals i buf start lastPos) lastPos 0
          x  => case term `at` x of
            Nothing => inner prev last     start lastPos vals k x
            Just i  => inner prev (Just i) start k       vals k x

lexFrom (L ss nxt t) (LST cur prev) pos buf =
  assert_total $ loop nxt t buf prev [<] pos cur

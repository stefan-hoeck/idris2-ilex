module Text.ILex.Runner

import public Data.Array.Core
import public Data.Array.Indexed
import public Data.ByteString
import public Data.Linear.Token
import public Data.List
import public Data.Vect
import public Text.ILex.RExp

import Control.Monad.State

import Data.Buffer
import Data.Buffer.Core
import Data.Buffer.Indexed
import Data.SortedMap
import Derive.Prelude

import Text.ILex.Char.UTF8
import Text.ILex.Internal.DFA
import Text.ILex.Internal.Types

%default total
%language ElabReflection

||| A discrete finite automaton (DFA) encoded as
||| an array of state transitions plus an array
||| describing the terminal states.
public export
record Lexer a where
  constructor L
  ||| Number of non-zero states in the automaton.
  states : Nat

  ||| State transitions matrix.
  |||
  ||| If `cur` is the current state (encoded as a `Fin (S states)`
  ||| and `b` is the current input byte, the next state is determined
  ||| by `next[cur][b]` (in pseudo C-syntax).
  next   : IArray (S states) (IArray 256 (Fin (S states)))

  ||| Terminal states and the corresponding conversions.
  term   : IArray (S states) (Maybe $ Conv a)

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

||| Like `lexChunk` but processes data from a single buffer.
export %inline
lex : {n : _} -> (l : Lexer a) -> IBuffer n -> LexRes l.states a
lex l buf = lexChunk l init (n ** buf)

||| Like `lexChunk` but processes data from a single buffer.
export
lexString : (l : Lexer a) -> String -> LexRes l.states a
lexString l s = lex l (fromString s)

bvcopy : {n : _} -> ByteVect n -> IBuffer n
bvcopy (BV buf o lte) =
  Buffer.Core.alloc n $ \mb,t =>
   let _ # t := Buffer.Core.icopy buf o 0 n mb t
    in unsafeFreeze mb t

||| Like `lexChunk` but processes data from a single byte string.
export
lexBytes : (l : Lexer a) -> ByteString -> LexRes l.states a
lexBytes l (BS s $ BV buf 0 lte) = lex l (take s buf)
lexBytes l (BS s bv)             = lex l (bvcopy bv)

--------------------------------------------------------------------------------
-- Lexer Generator
--------------------------------------------------------------------------------

emptyRow : IArray 256 (Fin (S n))
emptyRow = fill _ 0

emptyLexer : Lexer a
emptyLexer = L 0 (fill _ emptyRow) (fill _ Nothing)

term : SortedMap Nat a -> Node -> Maybe (Nat, Maybe a)
term m (N _ []     _) = Nothing
term m (N n (t::_) _) = ((n,) . Just) <$> lookup t m

node : {n : _} -> Node -> (Nat, IArray 256 (Fin (S n)))
node (N k _ out) = (k, fromPairs _ 0 $ mapMaybe pair (out >>= transitions))
  where
    pair : (Bits8,Nat) -> Maybe (Nat, Fin (S n))
    pair (b,t) = (cast b,) <$> tryNatToFin t

export covering
lexer : (m : TokenMap (Conv a)) -> (0 p : NonEmpty m) => Lexer a
lexer m =
  let M tms graph := machine (toDFA m toByteRanges)
      nodes       := values graph
      S len       := length nodes | 0 => emptyLexer
      terms       := fromPairs (S len) Nothing (mapMaybe (term tms) nodes)
      trans       := fromPairs (S len) emptyRow (map node nodes)
   in L len trans terms

--------------------------------------------------------------------------------
-- Lexer run loop
--------------------------------------------------------------------------------

app :
     {n : _}
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
app prev sx (Txt f)     buf from till =
  let bv := fromIBuffer buf
      bs := BS _ $ substringFromTo from (ixToNat ix) {lt = ixLT ix} bv
   in sx :< f (prev <+> bs)
app prev sx _           buf from till = sx

parameters {0 a      : Type}
           {0 states : Nat}
           {n        : Nat}
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
      Nothing => EOI (ixToNat x)
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

lexChunk (L ss nxt t) (LST cur prev) (n ** buf) =
  assert_total $ loop nxt t buf prev [<] n cur

module Text.ILex.Lexer

import public Data.Array
import public Text.ILex.RExp
import public Data.List

import Control.Monad.State

import Data.SortedMap
import Derive.Prelude

import Text.ILex.Char.UTF8
import Text.ILex.Internal.DFA
import Text.ILex.Internal.Types

%default total
%language ElabReflection

||| An array of arrays describing a lexer's state machine.
public export
0 Stepper : Nat -> Type
Stepper states = IArray (S states) (IArray 256 (Fin (S states)))

||| A discrete finite automaton (DFA) encoded as
||| an array of state transitions plus an array
||| describing the terminal states.
public export
record Lexer e a where
  constructor L
  ||| Number of non-zero states in the automaton.
  states : Nat

  ||| State transitions matrix.
  |||
  ||| If `cur` is the current state (encoded as a `Fin (S states)`
  ||| and `b` is the current input byte, the next state is determined
  ||| by `next[cur][b]` (in pseudo C-syntax).
  next   : Stepper states

  ||| Terminal states and the corresponding conversions.
  term   : IArray (S states) (Maybe $ Conv e a)

  ||| End of input token (if any)
  eoi    : Maybe a

--------------------------------------------------------------------------------
-- Lexer Generator
--------------------------------------------------------------------------------

emptyRow : IArray 256 (Fin (S n))
emptyRow = fill _ 0

emptyLexer : Lexer e a
emptyLexer = L 0 (fill _ emptyRow) (fill _ Nothing) Nothing

term : SortedMap Nat a -> Node -> Maybe (Nat, Maybe a)
term m (N _ []     _) = Nothing
term m (N n (t::_) _) = ((n,) . Just) <$> lookup t m

node : {n : _} -> Node -> (Nat, IArray 256 (Fin (S n)))
node (N k _ out) = (k, fromPairs _ 0 $ mapMaybe pair (out >>= transitions))
  where
    pair : (Bits8,Nat) -> Maybe (Nat, Fin (S n))
    pair (b,t) = (cast b,) <$> tryNatToFin t

||| A lexer operating on raw bytes.
export
byteLexer : (m : TokenMap8 (Conv e a)) -> (0 p : NonEmpty m) => Lexer e a
byteLexer m =
  let M tms graph := assert_total $ machine (toDFA m)
      nodes       := values graph
      S len       := length nodes | 0 => emptyLexer
      terms       := fromPairs (S len) Nothing (mapMaybe (term tms) nodes)
      trans       := fromPairs (S len) emptyRow (map node nodes)
   in L len trans terms Nothing

||| A utf-8 aware lexer operating on text.
export
lexer : (m : TokenMap (Conv e a)) -> (0 p : NonEmpty m) => Lexer e a
lexer (p::ps) = byteLexer (toUTF8 p :: map toUTF8 ps)

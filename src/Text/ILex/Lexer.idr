module Text.ILex.Lexer

import public Data.Array
import public Text.ILex.Error
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
record DFA e c a where
  constructor D
  ||| Number of non-zero states in the automaton.
  states : Nat

  ||| State transitions matrix.
  |||
  ||| If `cur` is the current state (encoded as a `Fin (S states)`
  ||| and `b` is the current input byte, the next state is determined
  ||| by `next[cur][b]` (in pseudo C-syntax).
  next   : Stepper states

  ||| Terminal states and the corresponding conversions.
  term   : IArray (S states) (Conv e c a)

  ||| End of input token (if any)
  eoi    : Maybe (Either (InnerError a e) a)

export %inline
setEOI : a -> DFA e c a -> DFA e c a
setEOI v = {eoi := Just (Right v)}

export %inline
errEOI : InnerError a e -> DFA e c a -> DFA e c a
errEOI x = {eoi := Just (Left x)}

||| A lexer is a system of automata, where each
||| lexicographic token determines the next automaton
||| to use.
public export
record Lexer e c a where
  constructor L
  init : c
  dfa  : c -> DFA e c a

export
lexer : DFA e () a -> Lexer e () a
lexer dfa = L () (const dfa)

--------------------------------------------------------------------------------
-- Lexer Generator
--------------------------------------------------------------------------------

emptyRow : IArray 256 (Fin (S n))
emptyRow = fill _ 0

emptyDFA : DFA e c a
emptyDFA = D 0 (fill _ emptyRow) (fill _ Bottom) Nothing

term : SortedMap Nat a -> Node -> Maybe (Nat, a)
term m (N _ []     _) = Nothing
term m (N n (t::_) _) = (n,) <$> lookup t m

node : {n : _} -> Node -> (Nat, IArray 256 (Fin (S n)))
node (N k _ out) = (k, fromPairs _ 0 $ mapMaybe pair (out >>= transitions))
  where
    pair : (Bits8,Nat) -> Maybe (Nat, Fin (S n))
    pair (b,t) = (cast b,) <$> tryNatToFin t

||| A DFA operating on raw bytes.
export
byteDFA : (m : TokenMap8 (Conv e c a)) -> (0 p : NonEmpty m) => DFA e c a
byteDFA m =
  let M tms graph := assert_total $ machine (toDFA m)
      nodes       := values graph
      S len       := length nodes | 0 => emptyDFA
      terms       := fromPairs (S len) Bottom (mapMaybe (term tms) nodes)
      trans       := fromPairs (S len) emptyRow (map node nodes)
   in D len trans terms Nothing

||| A utf-8 aware DFA operating on text.
export
dfa : (m : TokenMap (Conv e c a)) -> (0 p : NonEmpty m) => DFA e c a
dfa (p::ps) = byteDFA (toUTF8 p :: map toUTF8 ps)

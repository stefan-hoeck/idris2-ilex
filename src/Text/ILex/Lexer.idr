module Text.ILex.Lexer

import public Data.Array
import public Text.ILex.Bounds
import public Text.ILex.Error
import public Text.ILex.RExp
import public Data.List

import Control.Monad.State

import Data.ByteString
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
||| describing the terminal token states.
public export
record DFA e t where
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
  term   : IArray (S states) (Tok e t)

public export
0 ParseRes : (b,e,s,t : Type) -> Type
ParseRes b e s t = Either (GenBounded b $ InnerError t e) s

public export
record Input b s t where
  constructor I
  token  : t
  state  : s
  bounds : b

||| A parser is a system of automata, where each
||| lexicographic token determines the next automaton
||| state plus lexer to use.
public export
record Parser b e t a where
  constructor P
  {0 state : Type}
  init     : state
  lex      : state -> DFA e t
  step     : Input b state t -> ParseRes b e state t
  chunk    : state -> (state, Maybe a)
  eoi      : b -> state -> ParseRes b e a t

public export
0 Lexer : (b,e,t : Type) -> Type
Lexer b e t = Parser b e t (List $ GenBounded b t)

export
lexer : DFA e t -> Lexer b e t
lexer dfa =
  P [<] (const dfa)
    (\(I v st bs) => Right (st:<B v bs))
    (\st => ([<], Just $ st <>> []))
    (\_ => Right . (<>> []))

--------------------------------------------------------------------------------
-- Lexer Generator
--------------------------------------------------------------------------------

emptyRow : IArray 256 (Fin (S n))
emptyRow = fill _ 0

emptyDFA : DFA e a
emptyDFA = L 0 (fill _ emptyRow) (fill _ Bottom)

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
byteDFA : (m : TokenMap8 (Tok e a)) -> (0 p : NonEmpty m) => DFA e a
byteDFA m =
  let M tms graph := assert_total $ machine (toDFA m)
      nodes       := values graph
      S len       := length nodes | 0 => emptyDFA
      terms       := fromPairs (S len) Bottom (mapMaybe (term tms) nodes)
      trans       := fromPairs (S len) emptyRow (map node nodes)
   in L len trans terms

||| A utf-8 aware DFA operating on text.
export
dfa : (m : TokenMap (Tok e a)) -> (0 p : NonEmpty m) => DFA e a
dfa (p::ps) = byteDFA (toUTF8 p :: map toUTF8 ps)

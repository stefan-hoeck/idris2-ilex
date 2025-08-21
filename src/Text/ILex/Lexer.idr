module Text.ILex.Lexer

import public Data.Array
import public Text.ILex.Bounds
import public Text.ILex.Error
import public Text.ILex.RExp
import public Data.List

import Control.Monad.State

import Data.ByteString
import Data.Linear.Traverse1
import Data.SortedMap as SM
import Derive.Prelude

import Text.ILex.Char.UTF8
import Text.ILex.Internal.DFA
import Text.ILex.Internal.Types

%default total
%language ElabReflection

public export
data Transition : (n : Nat) -> (a : Type) -> Type where
  KeepT  : Transition n a
  Done   : a -> Transition n a
  Keep   : Transition n a
  Move   : Fin (S n) -> Transition n a
  MoveT  : Fin (S n) -> a -> Transition n a
  Bottom : Transition n a

||| An array of arrays describing a lexer's state machine.
public export
0 ByteStep : Nat -> (a : Type) -> Type
ByteStep n a = IArray 256 (Transition n a)

||| An array of arrays describing a lexer's state machine.
public export
0 Stepper : Nat -> (a : Type) -> Type
Stepper n a = IArray (S n) (ByteStep n a)

||| A discrete finite automaton (DFA) encoded as
||| an array of state transitions plus an array
||| describing the terminal token states.
public export
record DFA a where
  constructor L
  ||| Number of non-zero states in the automaton.
  states : Nat

  ||| State transitions matrix.
  |||
  ||| If `cur` is the current state (encoded as a `Fin (S states)`
  ||| and `b` is the current input byte, the next state is determined
  ||| by `next[cur][b]` (in pseudo C-syntax).
  next   : Stepper states a

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
  lex      : state -> DFA (Tok e t)
  step     : Input b state t -> ParseRes b e state t
  chunk    : state -> (state, Maybe a)
  eoi      : b -> state -> ParseRes b e a t

public export
0 Lexer : (b,e,t : Type) -> Type
Lexer b e t = Parser b e t (List $ GenBounded b t)

export
lexer : DFA (Tok e t) -> Lexer b e t
lexer dfa =
  P [<] (const dfa)
    (\(I v st bs) => Right (st:<B v bs))
    (\st => ([<], Just $ st <>> []))
    (\_ => Right . (<>> []))

--------------------------------------------------------------------------------
-- Lexer Generator
--------------------------------------------------------------------------------

emptyRow : ByteStep n a
emptyRow = fill _ Bottom

emptyDFA : DFA a
emptyDFA = L 0 (fill _ emptyRow)

-- Extracts the terminal state of a node
-- `Left` : This is a final node with no more state transitions
-- `Right`: This node has additional state transitions
terminals : SortedMap Nat a -> Node -> Maybe (Nat, Either a a)
terminals m (N n (t::_) []) = ((n,) . Left) <$> lookup t m
terminals m (N n (t::_) _)  = ((n,) . Right) <$> lookup t m
terminals _ _               = Nothing

nonFinal : SortedMap Nat (Either a a) -> Node -> Maybe Node
nonFinal m n =
  case lookup n.pos m of
    Just (Left _) => Nothing
    _             => Just n

index : {n : _} -> List (Nat,Node) -> SortedMap Nat (Fin (S n))
index ns = SM.fromList $ mapMaybe (\(x,n) => (n.pos,) <$> tryNatToFin x) ns

node :
     SortedMap Nat (Either a a)
  -> (index : SortedMap Nat (Fin (S n)))
  -> (node  : (Nat,Node))
  -> (Nat, ByteStep n a)
node terms index (ix, N me _ out) =
  (ix, fromPairs _ Bottom $ mapMaybe pair (out >>= transitions))
  where
    pair : (Bits8,Nat) -> Maybe (Nat, Transition n a)
    pair (b,tgt) =
      case lookup tgt terms of
        Nothing        => case tgt == me of
          True  => Just (cast b, Keep)
          False => ((cast b,) . Move) <$> lookup tgt index
        Just (Left x)  => Just (cast b, Done x)
        Just (Right x) => case tgt == me of
          True  => Just (cast b, KeepT)
          False => ((cast b,) . (`MoveT` x)) <$> lookup tgt index

||| A DFA operating on raw bytes.
export
byteDFA : (m : TokenMap8 a) -> (0 p : NonEmpty m) => DFA a
byteDFA m =
  let M tms graph := assert_total $ machine (toDFA m)
      terms       := SM.fromList (mapMaybe (terminals tms) (values graph))
      nodes       := zipWithIndex $ mapMaybe (nonFinal terms) (values graph)
      S len       := length nodes | 0 => emptyDFA
      ix          := index nodes
      trans       := fromPairs (S len) emptyRow (map (node terms ix) nodes)
   in L len trans

||| A utf-8 aware DFA operating on text.
export
dfa : (m : TokenMap a) -> (0 p : NonEmpty m) => DFA a
dfa (p::ps) = byteDFA (toUTF8 p :: map toUTF8 ps)

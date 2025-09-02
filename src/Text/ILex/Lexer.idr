module Text.ILex.Lexer

import public Data.Array
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
  Keep   : Transition n a
  Done   : a -> Transition n a
  Move   : Fin (S n) -> a -> Transition n a
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
     (dflt : a)
  -> SortedMap Nat (Either a a)
  -> (index : SortedMap Nat (Fin (S n)))
  -> (node  : (Nat,Node))
  -> (Nat, ByteStep n a)
node dflt terms index (ix, N me _ out) =
  (ix, fromPairs _ Bottom $ mapMaybe pair (out >>= transitions))
  where
    pair : (Bits8,Nat) -> Maybe (Nat, Transition n a)
    pair (b,tgt) =
      case lookup tgt terms of
        Nothing        => case tgt == me of
          True  => Just (cast b, Keep)
          False => ((cast b,) . (`Move` dflt)) <$> lookup tgt index
        Just (Left x)  => Just (cast b, Done x)
        Just (Right x) => case tgt == me of
          True  => Just (cast b, Keep)
          False => ((cast b,) . (`Move` x)) <$> lookup tgt index

||| A DFA operating on raw bytes.
export
byteDFA : a -> (m : TokenMap8 a) -> DFA a
byteDFA v m =
  let M tms graph := assert_total $ machine (toDFA m)
      terms       := SM.fromList (mapMaybe (terminals tms) (values graph))
      nodes       := zipWithIndex $ mapMaybe (nonFinal terms) (values graph)
      S len       := length nodes | 0 => emptyDFA
      ix          := index nodes
      trans       := fromPairs (S len) emptyRow (map (node v terms ix) nodes)
   in L len trans

||| A utf-8 aware DFA operating on text.
export
dfa : a -> (m : TokenMap a) -> DFA a
dfa v = byteDFA v . map toUTF8

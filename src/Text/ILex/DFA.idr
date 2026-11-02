module Text.ILex.DFA

import public Data.Array
import public Data.List
import public Text.ILex.RExp

import Data.Linear.Traverse1
import Control.Monad.State

import Data.SortedMap as SM

import Text.ILex.Char.UTF8
import Text.ILex.Internal.DFA
import Text.ILex.Internal.Types

%default total

public export
data Res : Type -> Type where
  Run : (res : a) -> Res a
  Ign : Res a
  Err : Res a

public export
data Transition : (n : Nat) -> Type -> Type where
  Keep   : Transition n a
  Done   : (val : a) -> Transition n a
  Ignore : Transition n a
  Move   : Fin (S n) -> (val : a) -> Transition n a
  MoveI  : Fin (S n) -> Transition n a
  MoveE  : Fin (S n) -> Transition n a
  Bottom : Transition n a

move : Res a -> Fin (S n) -> Transition n a
move (Run f) y = Move y f
move Ign     y = MoveI y
move Err     y = Bottom

done : Res a -> Transition n a
done (Run f) = Done f
done Ign     = Ignore
done Err     = Bottom

||| An array of arrays describing a lexer's state machine.
public export
0 ByteTrans : Nat -> Type -> Type
ByteTrans n a = IArray 256 (Transition n a)

||| An array of arrays describing a lexer's state machine.
public export
0 Machine : Nat -> Type -> Type
Machine n a = IArray (S n) (ByteTrans n a)

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
  next   : Machine states a

--------------------------------------------------------------------------------
-- Lexer Generator
--------------------------------------------------------------------------------

public export
0 Results : Type -> Type
Results a = TokenMap (Res a)

emptyRow : ByteTrans n a
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
     SortedMap Nat (Either (Res a) (Res a))
  -> (index : SortedMap Nat (Fin (S n)))
  -> (node  : (Nat,Node))
  -> (Nat, ByteTrans n a)
node terms index (ix, N me _ out) =
  (ix, fromPairs _ Bottom $ mapMaybe pair (out >>= transitions))
  where
    pair : (Bits8,Nat) -> Maybe (Nat, Transition n a)
    pair (b,tgt) =
      case lookup tgt terms of
        Nothing        => case tgt == me of
          True  => Just (cast b, Keep)
          False => ((cast b,) . MoveE) <$> lookup tgt index
        Just (Left f)  => Just (cast b, done f)
        Just (Right f) => case tgt == me of
          True  => Just (cast b, Keep)
          False => ((cast b,) . (move f)) <$> lookup tgt index

||| A DFA operating on raw bytes.
export
byteDFA : (m : TokenMap8 (Res a)) -> DFA a
byteDFA m =
  let M tms graph := assert_total $ machine (toDFA m)
      terms       := SM.fromList (mapMaybe (terminals tms . snd) graph)
      nodes       := zipWithIndex $ mapMaybe (nonFinal terms . snd) graph
      S len       := length nodes | 0 => emptyDFA
      ix          := index nodes
      trans       := fromPairs (S len) emptyRow (map (node terms ix) nodes)
   in L len trans

||| A utf-8 aware DFA operating on text.
export
dfa : Results a -> DFA a
dfa = byteDFA . map toUTF8

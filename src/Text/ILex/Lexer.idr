module Text.ILex.Lexer

import public Data.Array
import public Data.List
import public Data.Prim.Bits32
import public Text.ILex.RExp

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
record Index (n : Bits32) where
  constructor I
  val : Bits32
  {auto 0 prf : val < n}

%runElab deriveIndexed "Index" [Show,Eq,Ord]

public export
fromInteger : (n : Integer) -> (0 p : cast n < r) => Index r
fromInteger n = I (cast n)

public export
Ini : (0 prf : 0 < n) => Index n
Ini = I 0

public export
0 Step1 : (q : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
Step1 q r s = (1 sk : R1 q (s q)) -> R1 q (Index r)

export %inline
toState : Index r -> Step1 q r s
toState v = \(_ # t) => v # t

public export
data Transition :
     (n : Nat)
  -> (q : Type)
  -> (r : Bits32)
  -> (s : Type -> Type)
  -> Type where
  Keep   : Transition n q r s
  Done   : Step1 q r s -> Transition n q r s
  DoneBS : Step1 q r s -> Transition n q r s
  Move   : Fin (S n) -> Step1 q r s -> Transition n q r s
  MoveE  : Fin (S n) -> Transition n q r s
  Bottom : Transition n q r s

||| An array of arrays describing a lexer's state machine.
public export
0 ByteStep : Nat -> (q : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
ByteStep n q r s = IArray 256 (Transition n q r s)

||| An array of arrays describing a lexer's state machine.
public export
0 Stepper : Nat -> (q : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
Stepper n q r s = IArray (S n) (ByteStep n q r s)

||| A discrete finite automaton (DFA) encoded as
||| an array of state transitions plus an array
||| describing the terminal token states.
public export
record DFA q r s where
  constructor L
  ||| Number of non-zero states in the automaton.
  states : Nat

  ||| State transitions matrix.
  |||
  ||| If `cur` is the current state (encoded as a `Fin (S states)`
  ||| and `b` is the current input byte, the next state is determined
  ||| by `next[cur][b]` (in pseudo C-syntax).
  next   : Stepper states q r s

--------------------------------------------------------------------------------
-- Lexer Generator
--------------------------------------------------------------------------------

public export
data Step : (q : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type where
  Go  : Step1 q r s -> Step q r s
  Rd  : Step1 q r s -> Step q r s

public export
0 Steps : (q : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
Steps q r s = TokenMap (Step q r s)

emptyRow : ByteStep n q r s
emptyRow = fill _ Bottom

emptyDFA : DFA q r s
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
     SortedMap Nat (Either (Step q r s) (Step q r s))
  -> (index : SortedMap Nat (Fin (S n)))
  -> (node  : (Nat,Node))
  -> (Nat, ByteStep n q r s)
node terms index (ix, N me _ out) =
  (ix, fromPairs _ Bottom $ mapMaybe pair (out >>= transitions))
  where
    pair : (Bits8,Nat) -> Maybe (Nat, Transition n q r s)
    pair (b,tgt) =
      case lookup tgt terms of
        Nothing        => case tgt == me of
          True  => Just (cast b, Keep)
          False => ((cast b,) . MoveE) <$> lookup tgt index
        Just (Left $ Go f)  => Just (cast b, Done f)
        Just (Left $ Rd f)  => Just (cast b, DoneBS f)
        Just (Right $ Go f) => case tgt == me of
          True  => Just (cast b, Keep)
          False => ((cast b,) . (`Move` f)) <$> lookup tgt index
        Just (Right $ Rd f) => case tgt == me of
          True  => Just (cast b, Keep)
          False => ((cast b,) . (`Move` f)) <$> lookup tgt index

||| A DFA operating on raw bytes.
export
byteDFA : (m : TokenMap8 (Step q r s)) -> DFA q r s
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
dfa : Steps q r s -> DFA q r s
dfa = byteDFA . map toUTF8

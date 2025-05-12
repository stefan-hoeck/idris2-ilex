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
record Lexer a where
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
  term   : IArray (S states) (Maybe $ Conv a)

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

||| A lexer operating on raw bytes.
export
byteLexer : (m : TokenMap8 (Conv a)) -> (0 p : NonEmpty m) => Lexer a
byteLexer m =
  let M tms graph := assert_total $ machine (toDFA m)
      nodes       := values graph
      S len       := length nodes | 0 => emptyLexer
      terms       := fromPairs (S len) Nothing (mapMaybe (term tms) nodes)
      trans       := fromPairs (S len) emptyRow (map node nodes)
   in L len trans terms

||| A utf-8 aware lexer operating on text.
export
lexer : (m : TokenMap (Conv a)) -> (0 p : NonEmpty m) => Lexer a
lexer (p::ps) = byteLexer (toUTF8 p :: map toUTF8 ps)

--------------------------------------------------------------------------------
-- Bounded
--------------------------------------------------------------------------------

||| Upper and lower bounds of a region in a byte array.
public export
data Bounds : Type where
  Empty : Bounds
  BS    : (x,y : Nat) -> (0 prf : LTE x y) => Bounds

%runElab derive "Bounds" [Show,Eq,Ord]

0 appProof :
     (u,v,x,y : Nat)
  -> {auto p1 : LTE u v}
  -> {auto p2 : LTE x y}
  -> LTE (min u x) (max v y)

app : Bounds -> Bounds -> Bounds
app Empty     y       = y
app x         Empty   = x
app (BS u v) (BS x y) = BS (min u x) (max v y) @{appProof u v x y}

public export
record Bounded a where
  constructor B
  bounds : Bounds
  value  : a

%runElab derive "Bounded" [Show,Eq,Ord]

export %inline
Semigroup Bounds where (<+>) = app

export %inline
Monoid Bounds where neutral = Empty

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

0 notLTisLTE :
     (x,y : Nat)
  -> (prf : (compareNat x y == LT) === False)
  -> LTE y x
notLTisLTE 0     0     prf = LTEZero
notLTisLTE (S k) 0     prf = LTEZero
notLTisLTE (S k) (S j) prf = LTESucc (notLTisLTE k j prf)
notLTisLTE 0     (S k) prf impossible

0 notGTisLTE :
     (x,y : Nat)
  -> (prf : (compareNat x y == GT) === False)
  -> LTE x y
notGTisLTE 0     0     prf = LTEZero
notGTisLTE 0     (S k) prf = LTEZero
notGTisLTE (S k) (S j) prf = LTESucc (notGTisLTE k j prf)
notGTisLTE (S k) 0     prf impossible

0 minLemma : (u,x : Nat) -> LTE (min u x) u
minLemma u x with (compareNat u x == LT) proof eq
  _ | True  = reflexive
  _ | False = notLTisLTE u x eq

0 maxLemma : (v,y : Nat) -> LTE v (max v y)
maxLemma v y with (compareNat v y == GT) proof eq
  _ | True  = reflexive
  _ | False = notGTisLTE v y eq

appProof u v x y =
  transitive (transitive (minLemma u x) p1) (maxLemma v y)

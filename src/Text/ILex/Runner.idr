module Text.ILex.Runner

import public Data.Array.Core
import public Data.Array.Indexed
import public Data.ByteString
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

export
fromIPairs : (n : _) -> List (Bits8,Integer) -> IArray 256 (Fin (S n))
fromIPairs n = fromPairs 256 0 . mapMaybe adj
  where
    adj : (Bits8,Integer) -> Maybe (Nat, Fin (S n))
    adj (x,y) = (cast x,) <$> tryNatToFin (cast y)

public export
record Lexer a where
  constructor L
  states : Nat
  next   : IArray (S states * 256) (Fin (2 * (S states) + 1))
  term   : IArray (S states) (Maybe $ Conv a)

export %inline
lex : {n : _} -> Lexer a -> IBuffer n -> Either (Nat,Bits8) (List a)

export
lexString : Lexer a -> String -> Either (Nat,Bits8) (List a)
lexString l s = lex l (fromString s)

--------------------------------------------------------------------------------
-- FFI and black magic
--------------------------------------------------------------------------------

%foreign "scheme:(lambda (x y z) (vector-ref x (fx+ z (fx* y 256))))"
         "javascript:lambda:(x y z) => x[Number(y) * 256 + z]"
prim__get256 : AnyPtr -> Integer -> Bits8 -> AnyPtr

-- Note: The inner call to `believe_me` is based on the fact that `IArray`
--       is a newtype wrapper around raw array data. The outer call converts
--       the returned value which is guaranteed to be of the correct type.
--       It allows us to avoid adding one more (erased) argument to `prim__get256`.
%inline
get256 : IArray (S n * 256) a -> Fin (S n) -> Bits8 -> a
get256 arr x byte = believe_me (prim__get256 (believe_me arr) (cast x) byte)

-- A node is a terminal if its last bit has been set. This avoids an
-- array lookup and pattern match on a `Maybe`.
%inline
isTerminal : Fin (2 * (S n) + 1) -> Integer
isTerminal x = prim__and_Integer (cast x) 1

-- we get the state out by right shifting the value. Alas, this requires a
-- prim-op on `Integer`, and we'd like to avoid going from `Integer` to `Nat`
-- and use `natToFinLT`, because the cast from `Integer` to `Nat` makes sure
-- the integer is non-negative, but we know that already. So, it's
-- `believe_me` again, for the sake of performance.
getState : Fin (2 * (S n) + 1) -> Fin (S n)
getState n = believe_me (prim__shr_Integer (cast n) 1)

--------------------------------------------------------------------------------
-- Lexer Generator
--------------------------------------------------------------------------------

emptyLexer : Lexer a
emptyLexer = L 0 (fill _ 0) (fill _ Nothing)

term : SortedMap Nat a -> Node -> Maybe (Nat, Maybe a)
term m (N _ []     _) = Nothing
term m (N n (t::_) _) = ((n,) . Just) <$> lookup t m

pairs :
     {n : _}
  -> IArray (S n) (Maybe a)
  -> Node
  -> List (Nat, Fin (2 * (S n) + 1))
pairs arr (N k _ out) = mapMaybe pair (out >>= transitions)
  where
    termAdd : Nat -> Nat
    termAdd k =
      case tryNatToFin k >>= at arr of
        Nothing => 0
        Just _  => 1

    pair : (Bits8,Nat) -> Maybe (Nat, Fin (2 * (S n) + 1))
    pair (b,t) = (k * 256 + cast b,) <$> tryNatToFin (2 * t + termAdd t)

export covering
lexer : (m : TokenMap (Conv a)) -> (0 p : NonEmpty m) => Lexer a
lexer m =
  let M tms graph := machine (toDFA m toByteRanges)
      nodes       := values graph
      S len       := length nodes | 0 => emptyLexer
      terms       := fromPairs (S len) Nothing (mapMaybe (term tms) nodes)
      trans       := fromPairs (S len * 256) 0 (nodes >>= pairs terms)
   in L len trans terms

--------------------------------------------------------------------------------
-- Lexer run loop
--------------------------------------------------------------------------------

app :
     {n : _}
  -> SnocList a
  -> Maybe (Conv a)
  -> IBuffer n
  -> (from        : Nat)
  -> (0    till   : Nat)
  -> {auto ix     : Ix (S till) n}
  -> {auto 0  lte : LTE from (ixToNat ix)}
  -> SnocList a
app sx (Just $ Const val) buf from till = sx :< val
app sx (Just $ Txt f)     buf from till =
  let bv := fromIBuffer buf
      bs := BS _ $ substringFromTo from (ixToNat ix) {lt = ixLT ix} bv
   in sx :< f bs
app sx _                  buf from till = sx

parameters {0 a      : Type}
           {0 states : Nat}
           {n        : Nat}
           (next     : IArray (S states * 256) (Fin (2 * (S states) + 1)))
           (term     : IArray (S states) (Maybe $ Conv a))
           (buf      : IBuffer n)

  covering
  inner :
       (last        : Fin (S states))   -- last encountered terminal state
    -> (start       : Nat)              -- start of current token
    -> (lastPos     : Nat)              -- counter for last byte in `last`
    -> {auto y      : Ix (S lastPos) n} -- end position in the byte array of `last`
    -> (vals        : SnocList a)       -- accumulated tokens
    -> (pos         : Nat)              -- reverse position in the byte array
    -> {auto x      : Ix pos n}         -- position in the byte array
    -> {auto 0 lte1 : LTE start (ixToNat y)}
    -> {auto 0 lte2 : LTE start (ixToNat x)}
    -> (cur         : Fin (S states))   -- current automaton state
    -> Either (Nat,Bits8) (List a)

  -- Accumulates lexemes by applying the maximum munch strategy:
  -- The largest matched lexeme is consumed and kept.
  covering
  loop :
       (vals    : SnocList a)       -- accumulated tokens
    -> (pos     : Nat)              -- reverse position in the byte array
    -> {auto x  : Ix pos n}         -- position in the byte array
    -> Either (Nat,Bits8) (List a)
  loop vals 0     = Right (vals <>> [])
  loop vals (S k) =
    case get256 next FZ (buf `ix` k) of
      0 => Left (ixToNat x, buf `ix` k)
      s =>
        let st := getState s
         in case isTerminal s of
              1 => inner st (ixToNat x) k vals k st
              _ => inner 0  (ixToNat x) k vals k st

  inner last start lastPos vals 0     cur =
    case last of
      0 => Left (ixToNat x, 0)
      s => loop (app vals (term `at` s) buf start lastPos) lastPos
  inner last start lastPos vals (S k) cur =
    case get256 next cur (buf `ix` k) of
      0 => case last of
        0 => Left (ixToNat x, buf `ix` k)
        s => loop (app vals (term `at` s) buf start lastPos) lastPos
      s =>
        let st := getState s
         in case isTerminal s of
              1 => inner st   start k       vals k st
              _ => inner last start lastPos vals k st

lex (L ss nxt t) buf = assert_total $ loop nxt t buf [<] n

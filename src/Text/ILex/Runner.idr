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
  next   : IArray (S states) (IArray 256 (Fin (S states)))
  term   : IArray (S states) (Maybe $ Conv a)

export %inline
lex : {n : _} -> Lexer a -> IBuffer n -> Either (Nat,Bits8) (List a)

export
lexString : Lexer a -> String -> Either (Nat,Bits8) (List a)
lexString l s = lex l (fromString s)

-- --------------------------------------------------------------------------------
-- -- FFI and black magic
-- --------------------------------------------------------------------------------
--
-- %foreign "scheme:(lambda (x y z) (vector-ref x (fx+ z (fx* y 256))))"
--          "javascript:lambda:(x y z) => x[Number(y) * 256 + z]"
-- prim__get256 : AnyPtr -> Integer -> Bits8 -> AnyPtr
--
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
  -> SnocList a
  -> Conv a
  -> IBuffer n
  -> (from        : Nat)
  -> (0    till   : Nat)
  -> {auto ix     : Ix (S till) n}
  -> {auto 0  lte : LTE from (ixToNat ix)}
  -> SnocList a
app sx (Const val) buf from till = sx :< val
app sx (Txt f)     buf from till =
  let bv := fromIBuffer buf
      bs := BS _ $ substringFromTo from (ixToNat ix) {lt = ixLT ix} bv
   in sx :< f bs
app sx _                  buf from till = sx

parameters {0 a      : Type}
           {0 states : Nat}
           {n        : Nat}
           (next     : IArray (S states) (IArray 256 (Fin (S states))))
           (term     : IArray (S states) (Maybe $ Conv a))
           (buf      : IBuffer n)

  covering
  inner :
       (last        : Maybe $ Conv a)   -- last encountered terminal state
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
    case (next `at` 0) `atByte` (buf `ix` k) of
      0 => Left (ixToNat x, buf `ix` k)
      s => inner (term `at` s) (ixToNat x) k vals k s

  inner last start lastPos vals 0     cur =
    case last of
      Nothing => Left (ixToNat x, 0)
      Just i  => loop (app vals i buf start lastPos) lastPos
  inner last start lastPos vals (S k) cur =
    let arr  := next `at` cur
        byte := ix buf k
     in case arr `atByte` byte of
          FZ => case last of
            Nothing => Left (ixToNat x, buf `ix` k)
            Just i  => loop (app vals i buf start lastPos) lastPos
          x  => case term `at` x of
            Nothing => inner last     start lastPos vals k x
            Just i  => inner (Just i) start k       vals k x

lex (L ss nxt t) buf = assert_total $ loop nxt t buf [<] n

module Text.ILex.Runner

import public Data.ByteString
import public Data.Array.Core
import public Data.Array.Indexed
import public Data.Vect

import Data.Buffer
import Data.Buffer.Core
import Data.Buffer.Indexed
import Derive.Prelude

%default total
%language ElabReflection

export
fromIPairs : (n : _) -> List (Bits8,Integer) -> IArray 256 (Fin (S n))
fromIPairs n = fromPairs 256 0 . mapMaybe adj
  where
    adj : (Bits8,Integer) -> Maybe (Nat, Fin (S n))
    adj (x,y) = (cast x,) <$> tryNatToFin (cast y)

public export
data Info : Type -> Type where
  Ignore : Info a
  Const  : (val : a) -> Info a
  Txt    : (ByteString -> a) -> Info a

public export
record Lexer a where
  constructor L
  states : Nat
  next   : IArray (S states) (IArray 256 (Fin (S states)))
  term   : IArray (S states) (Maybe $ Info a)

app :
     {n : _}
  -> SnocList a
  -> Info a
  -> IBuffer n
  -> (from        : Nat)
  -> (0    till   : Nat)
  -> {auto ix     : Ix (S till) n}
  -> {auto 0  lte : LTE from (ixToNat ix)}
  -> SnocList a
app sx Ignore      buf from till = sx
app sx (Const val) buf from till = sx :< val
app sx (Txt f)     buf from till =
  let bv := fromIBuffer buf
      bs := BS _ $ substringFromTo from (ixToNat ix) {lt = ixLT ix} bv
   in sx :< f bs

parameters {0 a      : Type}
           {0 states : Nat}
           {n        : Nat}
           (next     : IArray (S states) (IArray 256 (Fin (S states))))
           (term     : IArray (S states) (Maybe $ Info a))
           (buf      : IBuffer n)

  covering
  inner :
       (last        : Maybe $ Info a)   -- last encountered terminal state
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

export %inline
lex : {n : _} -> Lexer a -> IBuffer n -> Either (Nat,Bits8) (List a)
lex (L ss nxt t) buf = assert_total $ loop nxt t buf [<] n

export
lexString : Lexer a -> String -> Either (Nat,Bits8) (List a)
lexString l s = lex l (fromString s)

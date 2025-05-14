module Text.ILex.Runner

import public Data.ByteString
import public Data.Linear.Token
import public Data.Vect
import public Text.ILex.Bounds
import public Text.ILex.Error
import public Text.ILex.Lexer

import Data.Buffer
import Data.Buffer.Core
import Data.Buffer.Indexed
import Derive.Prelude

%default total
%language ElabReflection

||| Lexing state.
|||
||| This encapsulates the current state as well as
||| the remainder of the previous chunk that marks
||| the beginning of the current token.
public export
record LexState (n : Nat) where
  constructor LST
  cur  : Fin (S n)
  prev : ByteString

%runElab deriveIndexed "LexState" [Show]

export
init : LexState n
init = LST 0 empty

public export
data LexRes : (n : Nat) -> Type -> Type -> Type where
  Err  : Bounds -> InnerError a e -> LexRes n e a
  Toks : LexState n -> List (Bounded a) -> LexRes n e a

%runElab derivePattern "LexRes" [I,P,P] [Show]

lexFrom :
     (l      : Lexer e a)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> LexRes l.states e a

||| Like `lexChunk` but processes data from a single buffer.
export %inline
lex : {n : _} -> (l : Lexer e a) -> IBuffer n -> LexRes l.states e a
lex l buf = lexFrom l n buf

||| Like `lexChunk` but processes data from a single buffer.
export
lexString : (l : Lexer e a) -> String -> LexRes l.states e a
lexString l s = lex l (fromString s)

offsetToIx : (o : Nat) -> Ix s (o+s)
offsetToIx 0     = IZ
offsetToIx (S k) = rewrite plusSuccRightSucc k s in IS (offsetToIx k)

||| Like `lexChunk` but processes data from a single byte string.
export %inline
lexBytes : (l : Lexer e a) -> ByteString -> LexRes l.states e a
lexBytes l (BS s $ BV buf o lte) =
  lexFrom l s {x = offsetToIx o} (take (o+s) buf)

--------------------------------------------------------------------------------
-- Lexer run loop
--------------------------------------------------------------------------------

export
toByteString :
     IBuffer n
  -> (from        : Nat)
  -> (0    till   : Nat)
  -> {auto ix     : Ix (S till) n}
  -> {auto 0  lte : LTE from (ixToNat ix)}
  -> ByteString
toByteString buf from till =
  let bv := fromIBuffer buf
   in BS _ $ substringFromTo from (ixToNat ix) {lt = ixLT ix} bv

parameters {0 e,a    : Type}
           {0 states : Nat}
           {0 n      : Nat}
           (next     : Stepper states)
           (term     : IArray (S states) (Maybe $ Conv e a))
           (buf      : IBuffer n)

  covering
  inner :
       (last        : Maybe $ Conv e a)     -- last encountered terminal state
    -> (start       : Nat)                  -- start of current token
    -> (lastPos     : Nat)                  -- counter for last byte in `last`
    -> {auto y      : Ix (S lastPos) n}     -- end position in the byte array of `last`
    -> (vals        : SnocList $ Bounded a) -- accumulated tokens
    -> (pos         : Nat)                  -- reverse position in the byte array
    -> {auto x      : Ix pos n}             -- position in the byte array
    -> {auto 0 lte1 : LTE start (ixToNat y)}
    -> {auto 0 lte2 : LTE start (ixToNat x)}
    -> (cur         : Fin (S states))       -- current automaton state
    -> LexRes states e a

  -- Accumulates lexemes by applying the maximum munch strategy:
  -- The largest matched lexeme is consumed and kept.
  covering
  loop :
       (vals    : SnocList $ Bounded a) -- accumulated tokens
    -> (pos     : Nat)                  -- reverse position in the byte array
    -> {auto x  : Ix pos n}             -- position in the byte array
    -> LexRes states e a
  loop vals 0     = Toks (LST 0 empty) (vals <>> [])
  loop vals (S k) =
    case (next `at` 0) `atByte` (buf `ix` k) of
      0 => Err (atPos $ ixToNat x) (Byte $ buf `ix` k)
      s => inner (term `at` s) (ixToNat x) k vals k s

  app :
       SnocList (Bounded a)
    -> Conv e a
    -> (from        : Nat)
    -> (till        : Nat)
    -> {auto ix     : Ix (S till) n}
    -> {auto 0  lte : LTE from (ixToNat ix)}
    -> LexRes states e a
  app sx c from till =
    let bs := BS from (ixToNat ix)
     in case c of
          Const v => loop (sx :< B v bs) till
          Ignore  => loop sx till
          Err   x => Err bs (Custom x)
          Txt   f => case f (toByteString buf from till) of
            Left  x => Err bs (Custom x)
            Right v => loop (sx :< B v bs) till

  inner last start lastPos vals 0     cur =
    case last of
      Nothing => Toks (LST cur (toByteString buf start lastPos)) (vals <>> [])
      Just i  => app vals i start lastPos
  inner last start lastPos vals (S k) cur =
    let arr  := next `at` cur
        byte := ix buf k
     in case arr `atByte` byte of
          FZ => case last of
            Nothing => Err (atPos $ ixToNat x) (Byte $ buf `ix` k)
            Just i  => app vals i start lastPos
          x  => case term `at` x of
            Nothing => inner last     start lastPos vals k x
            Just i  => inner (Just i) start k       vals k x

lexFrom (L ss nxt t) pos buf = assert_total $ loop nxt t buf [<] pos

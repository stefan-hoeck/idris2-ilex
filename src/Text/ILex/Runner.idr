module Text.ILex.Runner

import public Data.ByteString
import public Data.Linear.Token
import public Data.Vect
import public Text.ILex.Bounds
import public Text.ILex.Error
import public Text.ILex.FC
import public Text.ILex.Lexer

import Data.Buffer
import Data.Buffer.Core
import Data.Buffer.Indexed
import Derive.Prelude
import Text.ILex.Internal.Runner

%default total
%language ElabReflection

||| Result type of lexing a self-contained sequence of bytes.
public export
0 LexRes : (e,a : Type) -> Type
LexRes e a = Either (ParseError a e) (List (Bounded a))

lexFrom :
     {n      : Nat}
  -> (o      : Origin)
  -> (l      : Lexer e a)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> Either (ParseError a e) (List (Bounded a))

||| Tries to lex a whole byte vector into a list of bounded
||| tokens.
export %inline
lex : {n : _} -> Origin -> Lexer e a -> IBuffer n -> LexRes e a
lex o l buf = lexFrom o l n buf

||| Like `lex` but processes a UTF-8 string instead.
export %inline
lexString : Origin -> Lexer e a -> String -> LexRes e a
lexString o l s = lex o l (fromString s)

||| Like `lex` but processes a `ByteString` instead.
export
lexBytes : Origin -> Lexer e a -> ByteString -> LexRes e a
lexBytes o l (BS s $ BV buf off lte) =
  lexFrom o l s {x = offsetToIx off} (take (off+s) buf)


--------------------------------------------------------------------------------
-- Streaming
--------------------------------------------------------------------------------

||| Lexing state.
|||
||| This encapsulates the current state as well as
||| the remainder of the previous chunk that marks
||| the beginning of the current token.
public export
record LexState (n : Nat) where
  constructor LST
  pos  : StreamPos
  cur  : Fin (S n)
  prev : ByteString
  end  : StreamPos

%runElab deriveIndexed "LexState" [Show]

export
init : Origin -> LexState n
init o = LST (sp o 0 0) 0 empty (sp o 0 0)

||| Result of a partial lexing step: In such a step, we lex
||| till the end of a chunk of bytes, allowing for a remainder of
||| bytes that could not yet be identified as a tokens.
public export
0 PLexRes : (n : Nat) -> Type -> Type -> Type
PLexRes n e a = Either (StreamError a e) (LexState n, List (StreamBounded a))

plexFrom :
     (o      : Origin)
  -> (l      : Lexer e a)
  -> (st     : LexState l.states)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> PLexRes l.states e a

export %inline
plexBytes :
     (l : Lexer e a)
  -> Origin
  -> LexState l.states
  -> ByteString
  -> PLexRes l.states e a
plexBytes l o st (BS s $ BV buf off lte) =
  plexFrom o l st s {x = offsetToIx off} (take (off+s) buf)

--------------------------------------------------------------------------------
-- Lexer run loop
--------------------------------------------------------------------------------

parameters {0 e,a    : Type}
           {0 states : Nat}
           {0 n      : Nat}
           (next     : Stepper states)
           (term     : IArray (S states) (Conv e a))
           (buf      : IBuffer n)

  inner :
       (last        : Conv e a)             -- last encountered terminal state
    -> (start       : Nat)                  -- start of current token
    -> (lastPos     : Nat)                  -- counter for last byte in `last`
    -> {auto y      : Ix (S lastPos) n}     -- end position in the byte array of `last`
    -> (vals        : SnocList $ Bounded a) -- accumulated tokens
    -> (pos         : Nat)                  -- reverse position in the byte array
    -> {auto x      : Ix pos n}             -- position in the byte array
    -> {auto 0 lte1 : LTE start (ixToNat y)}
    -> {auto 0 lte2 : LTE start (ixToNat x)}
    -> (cur         : Fin (S states))       -- current automaton state
    -> Either (Bounded $ InnerError a e) (SnocList (Bounded a))

  -- Accumulates lexemes by applying the maximum munch strategy:
  -- The largest matched lexeme is consumed and kept.
  loop :
       (vals   : SnocList $ Bounded a) -- accumulated tokens
    -> (pos    : Nat)                  -- reverse position in the byte array
    -> {auto x : Ix pos n}             -- position in the byte array
    -> Either (Bounded $ InnerError a e) (SnocList (Bounded a))
  loop vals 0     = Right vals
  loop vals (S k) =
    case (next `at` 0) `atByte` (buf `ix` k) of
      0 => Left $ B (Byte $ buf `ix` k) (atPos $ ixToNat x)
      s => inner (term `at` s) (ixToNat x) k vals k s

  app :
       SnocList (Bounded a)
    -> Conv e a
    -> Lazy (InnerError a e)
    -> (from        : Nat)
    -> (till        : Nat)
    -> {auto ix     : Ix (S till) n}
    -> {auto 0  lte : LTE from (ixToNat ix)}
    -> Either (Bounded $ InnerError a e) (SnocList (Bounded a))
  app sx c err from till =
    let bs := BS from (ixToNat ix)
     in case c of
          Bottom  => Left $ B err (atPos $ ixToNat ix)
          Const v => loop (sx :< B v bs) till
          Ignore  => loop sx till
          Err   x => Left $ B (Custom x) bs
          Txt   f => case f (toByteString buf from till) of
            Left  x => Left $ B (Custom x) bs
            Right v => loop (sx :< B v bs) till

  inner last start lastPos vals 0     cur = app vals last EOI start lastPos
  inner last start lastPos vals (S k) cur =
    let arr  := next `at` cur
        byte := buf `ix` k
     in case arr `atByte` byte of
          FZ => app vals last (Byte byte) start lastPos
          x  => case term `at` x of
            Bottom => inner last start lastPos vals k x
            i      => inner i    start k       vals k x

lexFrom o l@(L ss nxt t _) pos buf =
  case loop nxt t buf [<] pos of
    Left (B x bs) => Left $ PE o bs (fromIBuffer buf) x
    Right vs      => appEOI l o (fromIBuffer buf) pos vs

--------------------------------------------------------------------------------
-- Streaming run loop
--------------------------------------------------------------------------------

parameters {0 e,a    : Type}
           {0 states : Nat}
           {0 n      : Nat}
           (o        : Origin)
           (next     : Stepper states)
           (term     : IArray (S states) (Conv e a))
           (buf      : IBuffer n)

  sinner :
       (spos        : StreamPos)
    -> (prev        : ByteString)
    -> (line        : Nat)
    -> (col         : Nat)
    -> (start       : Nat)                  -- start of current token
    -> (vals        : SnocList $ StreamBounded a) -- accumulated tokens
    -> (pos         : Nat)                  -- reverse position in the byte array
    -> {auto x      : Ix pos n}             -- position in the byte array
    -> {auto 0 lte2 : LTE start (ixToNat x)}
    -> (cur         : Fin (S states))       -- current automaton state
    -> PLexRes states e a

  sloop :
       (line   : Nat)
    -> (col    : Nat)
    -> (vals   : SnocList $ StreamBounded a) -- accumulated tokens
    -> (pos    : Nat)                  -- reverse position in the byte array
    -> {auto x : Ix (S pos) n}             -- position in the byte array
    -> PLexRes states e a
  sloop l c vals k =
    case buf `ix` k of
      10 => case (next `at` 0) `atByte` 10 of
        0 => Left (seByte o l c 10)
        s => sinner (sp o l c) empty (S l) 0 (ixToNat x) vals k s
      b  => case (next `at` 0) `atByte` b  of
        0 => Left (seByte o l c b)
        s => sinner (sp o l c) empty l (S c) (ixToNat x) vals k s

  sapp :
       (spos        : StreamPos)
    -> (prev        : ByteString)
    -> (line        : Nat)
    -> (col         : Nat)
    -> (byte        : Bits8)
    -> SnocList (StreamBounded a)
    -> Conv e a
    -> (from        : Nat)
    -> (till        : Nat)
    -> {auto ix     : Ix (S till) n}
    -> {auto 0  lte : LTE from (ixToNat ix)}
    -> PLexRes states e a
  sapp spos prev l c byte sx conv from till =
   let np := sp o l c
       bs := SB spos np
    in case conv of
         Bottom  => Left (seByte o l c byte)
         Const v => sloop l c (sx :< B v bs) till
         Ignore  => sloop l c sx             till
         Err   x => Left $ SE bs (Custom x)
         Txt   f => case f (prev <+> toByteString buf from till) of
           Left  x => Left $ SE bs (Custom x)
           Right v => sloop l c (sx :< B v bs) till

  sinner spos prev l c start vals 0       cur =
    Right (LST spos cur (prev <+> toBytes buf start 0) $ sp o l c, vals <>> [])
  sinner spos prev l c start vals (S k) cur =
    case ix buf k of
      10 => case (next `at` cur) `atByte` 10 of
        FZ => sapp spos prev l c 10 vals (term `at` cur) start k
        st => sinner spos prev (S l) 0 start vals k st
      b  => case (next `at` cur) `atByte` b of
        FZ => sapp spos prev l c b  vals (term `at` cur) start k
        st => sinner spos prev l (S c) start vals k st

plexFrom o (L ss nxt t _) (LST spos cur prev (SP oe $ P l c)) pos buf =
  case o == oe of
    True  => sinner o nxt t buf spos prev l c 0 [<] pos cur
    False => sinner o nxt t buf spos prev 0 0 0 [<] pos cur

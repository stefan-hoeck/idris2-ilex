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

||| Result of a partial lexing step: In such a step, we lex
||| till the end of a chunk of bytes, allowing for a remainder of
||| bytes that could not yet be identified as a tokens.
public export
data PLexRes : (n : Nat) -> Type -> Type -> Type where
  Err  : Bounds -> InnerError a e -> PLexRes n e a
  Toks : LexState n -> SnocList (Bounded a) -> PLexRes n e a

%runElab derivePattern "PLexRes" [I,P,P] [Show]

||| Result type of lexing a self-contained sequence of bytes.
public export
0 LexRes : (e,a : Type) -> Type
LexRes e a = Either (ParseError a e) (List (Bounded a))

plexFrom :
     (l      : Lexer e a)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> PLexRes l.states e a

lexFrom :
     {n      : Nat}
  -> (o      : Origin)
  -> (l      : Lexer e a)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> Either (ParseError a e) (List (Bounded a))
lexFrom o l pos buf =
  case plexFrom l pos buf of
    Err bs x               => Left (PE o bs (bytes buf pos) x)
    Toks (LST cur prev) sx => case prev.size of
      0 => appEOI o l buf pos sx
      _ => appLast o l buf pos cur prev sx


||| Partially lexes a string returning the remainder and
||| final state (if any).
export %inline
plex : {n : _} -> (l : Lexer e a) -> IBuffer n -> PLexRes l.states e a
plex l buf = plexFrom l n buf

||| Like `plex` but processes a UTF-8 string instead.
export
plexString : (l : Lexer e a) -> String -> PLexRes l.states e a
plexString l s = plex l (fromString s)

offsetToIx : (o : Nat) -> Ix s (o+s)
offsetToIx 0     = IZ
offsetToIx (S k) = rewrite plusSuccRightSucc k s in IS (offsetToIx k)

||| Like `plex` but processes data byte string
export %inline
plexBytes : (l : Lexer e a) -> ByteString -> PLexRes l.states e a
plexBytes l (BS s $ BV buf o lte) =
  plexFrom l s {x = offsetToIx o} (take (o+s) buf)

||| Like `plex` but tries to lex the whole string.
export
lex : {n : _} -> Origin -> Lexer e a -> IBuffer n -> LexRes e a
lex o l buf = lexFrom o l n buf

||| Like `plex` but processes a UTF-8 string instead.
export
lexString : Origin -> Lexer e a -> String -> LexRes e a
lexString o l s = lex o l (fromString s)

||| Like `plex` but processes a UTF-8 string instead.
export
lexBytes : Origin -> Lexer e a -> ByteString -> LexRes e a
lexBytes o l (BS s $ BV buf off lte) =
  lexFrom o l s {x = offsetToIx off} (take (off+s) buf)

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
    -> PLexRes states e a

  -- Accumulates lexemes by applying the maximum munch strategy:
  -- The largest matched lexeme is consumed and kept.
  covering
  loop :
       (vals   : SnocList $ Bounded a) -- accumulated tokens
    -> (pos    : Nat)                  -- reverse position in the byte array
    -> {auto x : Ix pos n}             -- position in the byte array
    -> PLexRes states e a
  loop vals 0     = Toks (LST 0 empty) vals
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
    -> PLexRes states e a
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
      Nothing => Toks (LST cur (toByteString buf start lastPos)) vals
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

plexFrom (L ss nxt t _) pos buf = assert_total $ loop nxt t buf [<] pos

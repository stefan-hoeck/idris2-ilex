-- TODO: Optimize `Txt` cases
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
import Text.ILex.Internal.Runner

%default total

||| Result type of lexing a self-contained sequence of bytes.
public export
0 ParseRes : (e,t,a : Type) -> Type
ParseRes e t a = Either (ParseError t e) a

parseFrom :
     {n      : Nat}
  -> (o      : Origin)
  -> (l      : Parser Bounds e t a)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> ParseRes e t a

||| Tries to lex a whole byte vector into a list of bounded
||| tokens.
export %inline
parse : {n : _} -> Origin -> Parser Bounds e t a -> IBuffer n -> ParseRes e t a
parse o l buf = parseFrom o l n buf

||| Like `lex` but processes a UTF-8 string instead.
export %inline
parseString : Origin -> Parser Bounds e t a -> String -> ParseRes e t a
parseString o l s = parse o l (fromString s)

||| Like `lex` but processes a `ByteString` instead.
export
parseBytes : Origin -> Parser Bounds e t a -> ByteString -> ParseRes e t a
parseBytes o l (BS s $ BV buf off lte) =
  parseFrom o l s {x = offsetToIx off} (take (off+s) buf)

--------------------------------------------------------------------------------
-- Streaming
--------------------------------------------------------------------------------

||| Lexing state.
|||
||| This encapsulates the current state as well as
||| the remainder of the previous chunk that marks
||| the beginning of the current token.
public export
record LexState (e,s,t : Type) where
  constructor LST
  state : s
  dfa   : DFA e t
  pos   : StreamPos
  cur   : ByteStep dfa.states e t
  tok   : Maybe (Tok e t)
  prev  : ByteString
  end   : StreamPos

export
init : Origin -> (p : Parser b e t a) -> LexState e p.state t
init o p =
 let dfa := p.lex p.init
  in LST p.init dfa (sp o 0 0) (dfa.next `at` 0) Nothing empty (sp o 0 0)

||| Result of a partial lexing step: In such a step, we lex
||| till the end of a chunk of bytes, allowing for a remainder of
||| bytes that could not yet be identified as a tokens.
public export
0 PLexRes : (e,s,t,a : Type) -> Type
PLexRes e s t a = Either (StreamError t e) (LexState e s t, Maybe a)

plexFrom :
     (o      : Origin)
  -> (p      : Parser StreamBounds e t a)
  -> (st     : LexState e p.state t)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> PLexRes e p.state t a

export %inline
pparseBytes :
     (p : Parser StreamBounds e t a)
  -> Origin
  -> LexState e p.state t
  -> ByteString
  -> PLexRes e p.state t a
pparseBytes l o st (BS s $ BV buf off lte) =
  plexFrom o l st s {x = offsetToIx off} (take (off+s) buf)

--------------------------------------------------------------------------------
-- Lexer run loop
--------------------------------------------------------------------------------

parameters {0 e,t,a : Type}
           {0 n     : Nat}
           (parser  : Parser Bounds e t a)
           (buf     : IBuffer n)

  inner :
       (dfa         : DFA e t)               -- current finite automaton
    -> (last        : Maybe $ Tok e t)       -- last encountered terminal state
    -> (start       : Nat)                   -- start of current token
    -> (lastPos     : Nat)                   -- counter for last byte in `last`
    -> {auto y      : Ix (S lastPos) n}      -- end position of `last` in the byte array
    -> (state       : parser.state)          -- accumulated state
    -> (pos         : Nat)                   -- reverse position in the byte array
    -> {auto x      : Ix pos n}              -- position in the byte array
    -> {auto 0 lte1 : LTE start (ixToNat y)}
    -> {auto 0 lte2 : LTE start (ixToNat x)}
    -> (cur         : ByteStep dfa.states e t)    -- current automaton state
    -> Either (Bounded $ InnerError t e) a

  -- Tries to create a new token from the current
  -- state and append it to the list of tokens.
  -- We need several pointers into the byte array:
  --   `from` is the start index of the token
  --   `ix`   is the end index of the token (`till` the corresponding reverse index)
  --   `now` is the current position needed in case of
  --   the encountered state being non-terminal
  app :
       (dfa         : DFA e t)
    -> (state       : parser.state)          -- state
    -> Tok e t                               -- terminal state to use
    -> (from        : Nat)                   -- start position of token
    -> (till        : Nat)                   -- reverse end position + 1
    -> {auto ix     : Ix (S till) n}         -- end position
    -> {auto 0  lte : LTE from (ixToNat ix)} -- current position
    -> Either (Bounded $ InnerError t e) a

  -- Accumulates lexemes by applying the maximum munch strategy:
  -- The largest matched lexeme is consumed and kept.
  -- This consumes at least one byte for the next token and
  -- immediately aborts with an error in case the current
  -- byte leads to the zero state.
  loop :
       (dfa    : DFA e t)                 -- current finite automaton
    -> (state  : parser.state)            -- accumulated tokens
    -> (pos    : Nat)                     -- reverse position in the byte array
    -> {auto x : Ix pos n}                -- position in the byte array
    -> Either (Bounded $ InnerError t e) a
  loop dfa state 0     = parser.eoi (atPos $ ixToNat x) state
  loop dfa state (S k) =
   let cur := dfa.next `at` 0
    in case cur `atByte` (buf `ix` k) of
         Done tok      => app dfa state tok (ixToNat x) k
         Move nxt      => inner dfa Nothing    (ixToNat x) k state k (dfa.next `at` nxt)
         MoveT nxt tok => inner dfa (Just tok) (ixToNat x) k state k (dfa.next `at` nxt)
         Keep          => inner dfa Nothing    (ixToNat x) k state k cur
         KeepT         => inner dfa Nothing    (ixToNat x) k state k cur
         Bottom        => Left $ B (Byte $ buf `ix` k) (atPos $ ixToNat x)

  app dfa state c from till =
    case c of
      Ignore  => loop dfa state till
      Const v => case parser.step (I v state bs) of
        Right s2 => loop (parser.lex s2) s2 till
        Left err => Left err
      Txt f => case f (toString $ toByteString buf from till) of
        Left  x => Left $ B (Custom x) bs
        Right v => case parser.step (I v state bs) of
          Right s2 => loop (parser.lex s2) s2 till
          Left err => Left err
      Bytes f => case f (toByteString buf from till) of
        Left  x => Left $ B (Custom x) bs
        Right v => case parser.step (I v state bs) of
          Right s2 => loop (parser.lex s2) s2 till
          Left err => Left err

    where
      bs : Bounds
      bs = BS from (ixToNat ix)

  inner dfa lst start lastPos state 0     cur =
    case lst of
      Just v  => app dfa state v start lastPos
      Nothing => Left $ B EOI (atPos $ ixToNat x)
  inner dfa lst start lastPos state (S k) cur =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         KeepT         => inner dfa lst        start k       state k cur
         Done tok      => app dfa state tok start k
         Keep          => inner dfa lst        start lastPos state k cur
         Move nxt      => inner dfa lst        start lastPos state k (dfa.next `at` nxt)
         MoveT nxt tok => inner dfa (Just tok) start k       state k (dfa.next `at` nxt)
         Bottom        => case lst of
           Just v  => app dfa state v start lastPos
           Nothing => Left $ B (Byte $ buf `ix` k) (atPos $ ixToNat x)

parseFrom o p pos buf =
  case loop p buf (p.lex p.init) p.init pos of
    Left (B x bs) => Left $ PE o bs (fromIBuffer buf) x
    Right v       => Right v

--------------------------------------------------------------------------------
-- Streaming run loop
--------------------------------------------------------------------------------

parameters {0 e,t,a : Type}
           {0 n     : Nat}
           (o       : Origin)
           (parser  : Parser StreamBounds e t a)
           (buf     : IBuffer n)

  covering
  sinner :
       (dfa         : DFA e t)
    -> (spos        : StreamPos)
    -> (tok         : Maybe (Tok e t))
    -> (prev        : ByteString)
    -> (cpos        : Position)
    -> (start       : Nat)                     -- start of current token
    -> (till        : Nat)
    -> (state       : parser.state)            -- accumulated tokens
    -> (pos         : Nat)                     -- reverse position in the byte array
    -> {auto x      : Ix pos n}                -- position in the byte array
    -> {auto xt     : Ix (S till) n}           -- position in the byte array
    -> {auto 0 lte1 : LTE start (ixToNat xt)}
    -> {auto 0 lte2 : LTE start (ixToNat x)}
    -> (cur         : ByteStep dfa.states e t) -- current automaton state
    -> PLexRes e parser.state t a

  covering %inline
  sloop :
       (dfa    : DFA e t)
    -> (spos   : StreamPos)
    -> (tok    : Maybe (Tok e t))
    -> (prev   : ByteString)
    -> (cpos   : Position)
    -> (state  : parser.state)         -- accumulated tokens
    -> (pos    : Nat)                  -- reverse position in the byte array
    -> {auto x : Ix pos n}             -- position in the byte array
    -> (cur    : ByteStep dfa.states e t) -- current automaton state
    -> PLexRes e parser.state t a

  covering
  sapp0 :
       (dfa         : DFA e t)
    -> (spos        : StreamPos)
    -> (prev        : ByteString)
    -> (cpos        : Position)
    -> parser.state
    -> Tok e t
    -> (pos         : Nat)
    -> {auto ix     : Ix pos n}
    -> PLexRes e parser.state t a
  sapp0 dfa spos prev cpos state conv pos =
   let np := SP o cpos
       bs := SB spos np
    in case conv of
         Ignore  => sloop dfa np Nothing empty cpos state pos (dfa.next `at` 0)
         Const v => case parser.step (I v state bs) of
           Right s2 =>
            let dfa2 := parser.lex s2
                cur  := dfa2.next `at` 0
             in sloop dfa2 np Nothing empty cpos s2 pos cur
           Left err => Left err
         Txt f => case f (toString prev) of
           Left  x => Left $ B (Custom x) bs
           Right v => case parser.step (I v state bs) of
             Right s2 =>
              let dfa2 := parser.lex s2
                  cur  := dfa2.next `at` 0
               in sloop dfa2 np Nothing empty cpos s2 pos cur
             Left err => Left err
         Bytes f => case f prev of
           Left  x => Left $ B (Custom x) bs
           Right v => case parser.step (I v state bs) of
             Right s2 =>
              let dfa2 := parser.lex s2
                  cur  := dfa2.next `at` 0
               in sloop dfa2 np Nothing empty cpos s2 pos cur
             Left err => Left err

  covering
  sapp :
       (dfa         : DFA e t)
    -> (spos        : StreamPos)
    -> (prev        : ByteString)
    -> (cpos        : Position)
    -> parser.state
    -> Tok e t
    -> (from        : Nat)
    -> (till        : Nat)
    -> {auto ix     : Ix (S till) n}
    -> {auto 0  lte : LTE from (ixToNat ix)}
    -> PLexRes e parser.state t a
  sapp dfa spos prev cpos state conv from till =
   let np := SP o cpos
       bs := SB spos np
    in case conv of
         Ignore  => sloop dfa np Nothing empty cpos state till (dfa.next `at` 0)
         Const v => case parser.step (I v state bs) of
           Right s2 =>
            let dfa2 := parser.lex s2
                cur  := dfa2.next `at` 0
             in sloop dfa2 np Nothing empty cpos s2 till cur
           Left err => Left err
         Txt f => case f (toString $ prev <+> toByteString buf from till) of
           Left  x => Left $ B (Custom x) bs
           Right v => case parser.step (I v state bs) of
             Right s2 =>
              let dfa2 := parser.lex s2
                  cur  := dfa2.next `at` 0
               in sloop dfa2 np Nothing empty cpos s2 till cur
             Left err => Left err
         Bytes f => case f (prev <+> toByteString buf from till) of
           Left  x => Left $ B (Custom x) bs
           Right v => case parser.step (I v state bs) of
             Right s2 =>
              let dfa2 := parser.lex s2
                  cur  := dfa2.next `at` 0
               in sloop dfa2 np Nothing empty cpos s2 till cur
             Left err => Left err

  sinner dfa spos tok prev cpos start till state 0       cur =
    let (s2,m) := parser.chunk state
        bytes  := prev <+> toBytes buf start 0
     in Right (LST s2 dfa spos cur tok bytes $ SP o cpos, m)
  sinner dfa spos tok prev cpos start till state (S k) cur =
   let b   := ix buf k
       cp2 := inc b cpos
    in case cur `atByte` b of
        KeepT        => sinner dfa spos tok        prev cp2 start k state k cur
        Done tok     => sapp dfa spos prev cp2 state tok start k
        Keep         => sinner dfa spos Nothing    prev cp2 start k state k cur
        Move st      => sinner dfa spos Nothing    prev cp2 start k state k (dfa.next `at` st)
        MoveT st tok => sinner dfa spos (Just tok) prev cp2 start k state k (dfa.next `at` st)
        Bottom       => case tok of
          Nothing => Left (seByte o cpos b)
          Just v  => sapp dfa spos prev cpos state v start till

  sloop dfa spos tok prev cpos state 0       cur =
    let (s2,m) := parser.chunk state
     in Right (LST s2 dfa spos cur tok prev $ SP o cpos, m)
  sloop dfa spos tok prev cpos state (S k) cur =
   let b   := ix buf k
       cp2 := inc b cpos
    in case cur `atByte` b of
        KeepT        => sinner dfa spos tok        prev cp2 (ixToNat x) k state k cur
        Done tok     => sapp dfa spos prev cp2 state tok (ixToNat x) k
        Keep         => sinner dfa spos Nothing    prev cp2 (ixToNat x) k state k cur
        Move st      => sinner dfa spos Nothing    prev cp2 (ixToNat x) k state k (dfa.next `at` st)
        MoveT st tok => sinner dfa spos (Just tok) prev cp2 (ixToNat x) k state k (dfa.next `at` st)
        Bottom       => case tok of
          Just v  => sapp0 dfa spos prev cpos state v (S k)
          Nothing => Left (seByte o cpos b)

plexFrom o lx (LST st dfa spos cur tok prev (SP oe cpos)) pos buf =
  assert_total $ case o == oe of
    True  => sloop o lx buf dfa spos tok prev cpos    st pos cur
    False => sloop o lx buf dfa spos tok prev (P 0 0) st pos cur

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
  prev  : ByteString
  end   : StreamPos

export
init : Origin -> (p : Parser b e t a) -> LexState e p.state t
init o p =
 let dfa := p.lex p.init
  in LST p.init dfa (sp o 0 0) (dfa.next `at` 0) empty (sp o 0 0)

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

  -- Reads next byte and determines the next automaton state
  -- If this is the zero state, we backtrack to the latest
  -- terminal state (in `last`), create a token from that
  -- (in `app`) and start with a new token (in `loop`).
  inner :
       (dfa         : DFA e t)               -- current finite automaton
    -> (start       : Nat)                   -- start of current token
    -> (state       : parser.state)          -- accumulated state
    -> (pos         : Nat)                   -- reverse position in the byte array
    -> {auto x      : Ix pos n}              -- position in the byte array
    -> {auto 0 lte2 : LTE start (ixToNat x)}
    -> (cur         : ByteStep dfa.states e t)    -- current automaton state
    -> Either (Bounded $ InnerError t e) a

  innerT :
       (dfa         : DFA e t)               -- current finite automaton
    -> (last        : Tok e t)               -- last encountered terminal state
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

--   -- Accumulates lexemes by applying the maximum munch strategy:
--   -- The largest matched lexeme is consumed and kept.
--   -- This consumes at least one byte for the next token and
--   -- immediately aborts with an error in case the current
--   -- byte leads to the zero state.
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
         Move nxt      => inner dfa (ixToNat x) state k (dfa.next `at` nxt)
         MoveT nxt tok => innerT dfa tok (ixToNat x) k state k (dfa.next `at` nxt)
         Keep          => inner dfa (ixToNat x) state k cur
         KeepT tok     => innerT dfa tok (ixToNat x) k state k cur
         Bottom        => Left $ B (Byte $ buf `ix` k) (atPos $ ixToNat x)

  app dfa state c from till =
    case c of
      Ignore  => loop dfa state till
      Const v => case parser.step (I v state bs) of
        Right s2 => loop (parser.lex s2) s2 till
        Left err => Left err
      Parse f => case f (toByteString buf from till) of
        Left  x => Left $ B (Custom x) bs
        Right v => case parser.step (I v state bs) of
          Right s2 => loop (parser.lex s2) s2 till
          Left err => Left err

    where
      bs : Bounds
      bs = BS from (ixToNat ix)

  inner dfa start state 0     cur = Left $ B EOI (atPos $ ixToNat x)
  inner dfa start state (S k) cur =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         KeepT tok     => innerT dfa tok start k state k cur
         Done tok      => app dfa state tok start k
         Keep          => inner dfa start state k cur
         Move nxt      => inner dfa start state k (dfa.next `at` nxt)
         MoveT nxt tok => innerT dfa tok start k state k (dfa.next `at` nxt)
         Bottom        => Left $ B (Byte $ buf `ix` k) (atPos $ ixToNat x)

  innerT dfa lst start lastPos state 0     cur =
    app dfa state lst start lastPos
  innerT dfa lst start lastPos state (S k) cur =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         KeepT tok     => innerT dfa tok start k       state k cur
         Done tok      => app dfa state tok start k
         Keep          => innerT dfa lst start lastPos state k cur
         Move nxt      => innerT dfa lst start lastPos state k (dfa.next `at` nxt)
         MoveT nxt tok => innerT dfa tok start k       state k (dfa.next `at` nxt)
         Bottom        => app dfa state lst start lastPos

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

  sinner :
       (dfa         : DFA e t)
    -> (spos        : StreamPos)
    -> (prev        : ByteString)
    -> (line        : Nat)
    -> (col         : Nat)
    -> (start       : Nat)                     -- start of current token
    -> (state       : parser.state)            -- accumulated tokens
    -> (pos         : Nat)                     -- reverse position in the byte array
    -> {auto x      : Ix pos n}                -- position in the byte array
    -> {auto 0 lte2 : LTE start (ixToNat x)}
    -> (cur         : ByteStep dfa.states e t) -- current automaton state
    -> PLexRes e parser.state t a

  sloop :
       (dfa    : DFA e t)
    -> (line   : Nat)
    -> (col    : Nat)
    -> (state  : parser.state)             -- accumulated tokens
    -> (pos    : Nat)                      -- reverse position in the byte array
    -> {auto x : Ix (S pos) n}             -- position in the byte array
    -> PLexRes e parser.state t a
--   sloop dfa l c state k =
--     case buf `ix` k of
--       10 => case (dfa.next `at` 0) `atByte` 10 of
--         0 => Left (seByte o l c 10)
--         s => sinner dfa (sp o l c) empty (S l) 0 (ixToNat x) state k s
--       b  => case (dfa.next `at` 0) `atByte` b  of
--         0 => Left (seByte o l c b)
--         s => sinner dfa (sp o l c) empty l (S c) (ixToNat x) state k s

--   sapp :
--        (dfa         : DFA e t)
--     -> (spos        : StreamPos)
--     -> (prev        : ByteString)
--     -> (line        : Nat)
--     -> (col         : Nat)
--     -> (byte        : Bits8)
--     -> parser.state
--     -> Tok e t
--     -> (from        : Nat)
--     -> (till        : Nat)
--     -> {auto ix     : Ix (S till) n}
--     -> {auto 0  lte : LTE from (ixToNat ix)}
--     -> PLexRes e parser.state t a
--   sapp dfa spos prev l c byte state conv from till =
--    let np := sp o l c
--        bs := SB spos np
--     in case conv of
--          Bottom  => Left (seByte o l c byte)
--          Ignore  => sloop dfa l c state             till
--          Const v => case parser.step (I v state bs) of
--            Right s2 => sloop (parser.lex s2) l c s2 till
--            Left err => Left err
--          Parse f => case f (prev <+> tillByteString buf from till) of
--            Left  x => Left $ B (Custom x) bs
--            Right v => case parser.step (I v state bs) of
--              Right s2 => sloop (parser.lex s2) l c s2 till
--              Left err => Left err
--
--   sinner dfa spos prev l c start state 0       cur =
--     let (s2,m) := parser.chunk state
--         bytes  := prev <+> toBytes buf start 0
--      in Right (LST s2 dfa spos cur bytes $ sp o l c, m)
--   sinner dfa spos prev l c start state (S k) cur =
--     case ix buf k of
--       10 => case (dfa.next `at` cur) `atByte` 10 of
--         FZ => sapp dfa spos prev l c 10 state (dfa.term `at` cur) start k
--         st => sinner dfa spos prev (S l) 0 start state k st
--       b  => case (dfa.next `at` cur) `atByte` b of
--         FZ => sapp dfa spos prev l c b  state (dfa.term `at` cur) start k
--         st => sinner dfa spos prev l (S c) start state k st

plexFrom o lx (LST st dfa spos cur prev (SP oe $ P l c)) pos buf =
  case o == oe of
    True  => sinner o lx buf dfa spos prev l c 0 st pos cur
    False => sinner o lx buf dfa spos prev 0 0 0 st pos cur

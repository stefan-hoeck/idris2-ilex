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
lexBytes : Origin -> Parser Bounds e t a -> ByteString -> ParseRes e t a
lexBytes o l (BS s $ BV buf off lte) =
  parseFrom o l s {x = offsetToIx off} (take (off+s) buf)

--------------------------------------------------------------------------------
-- Streaming
--------------------------------------------------------------------------------
--
-- ||| Lexing state.
-- |||
-- ||| This encapsulates the current state as well as
-- ||| the remainder of the previous chunk that marks
-- ||| the beginning of the current token.
-- public export
-- record LexState (e,c,a : Type) where
--   constructor LST
--   dfa  : DFA e c a
--   pos  : StreamPos
--   cur  : Fin (S dfa.states)
--   prev : ByteString
--   end  : StreamPos
--
-- export
-- init : Origin -> Lexer e c a -> LexState e c a
-- init o l = LST (l.dfa l.init) (sp o 0 0) 0 empty (sp o 0 0)
--
-- ||| Result of a partial lexing step: In such a step, we lex
-- ||| till the end of a chunk of bytes, allowing for a remainder of
-- ||| bytes that could not yet be identified as a tokens.
-- public export
-- 0 PLexRes : (e,c,a : Type) -> Type
-- PLexRes e c a = Either (StreamError a e) (LexState e c a, List (StreamBounded a))
--
-- plexFrom :
--      (o      : Origin)
--   -> (l      : Lexer e c a)
--   -> (st     : LexState e c a)
--   -> (pos    : Nat)
--   -> {auto x : Ix pos n}
--   -> IBuffer n
--   -> PLexRes e c a
--
-- export %inline
-- plexBytes :
--      (l : Lexer e c a)
--   -> Origin
--   -> LexState e c a
--   -> ByteString
--   -> PLexRes e c a
-- plexBytes l o st (BS s $ BV buf off lte) =
--   plexFrom o l st s {x = offsetToIx off} (take (off+s) buf)

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
    -> (last        : Tok e t)               -- last encountered terminal state
    -> (start       : Nat)                   -- start of current token
    -> (lastPos     : Nat)                   -- counter for last byte in `last`
    -> {auto y      : Ix (S lastPos) n}      -- end position of `last` in the byte array
    -> (state       : parser.state)          -- accumulated state
    -> (pos         : Nat)                   -- reverse position in the byte array
    -> {auto x      : Ix pos n}              -- position in the byte array
    -> {auto 0 lte1 : LTE start (ixToNat y)}
    -> {auto 0 lte2 : LTE start (ixToNat x)}
    -> (cur         : Fin (S dfa.states))    -- current automaton state
    -> Either (Bounded $ InnerError t e) a

--   -- Accumulates lexemes by applying the maximum munch strategy:
--   -- The largest matched lexeme is consumed and kept.
--   -- This consumes at least one byte for the next token and
--   -- immediately aborts with an error in case the current
--   -- byte leads to the zero state.
  loop :
       (dfa    : DFA e t)              -- current finite automaton
    -> (state  : parser.state)         -- accumulated tokens
    -> (pos    : Nat)                  -- reverse position in the byte array
    -> {auto x : Ix pos n}             -- position in the byte array
    -> Either (Bounded $ InnerError t e) a
  loop dfa state 0     = parser.eoi (atPos $ ixToNat x) state
  loop dfa state (S k) =
    case (dfa.next `at` 0) `atByte` (buf `ix` k) of
      0 => Left $ B (Byte $ buf `ix` k) (atPos $ ixToNat x)
      s => inner dfa (dfa.term `at` s) (ixToNat x) k state k s

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
    -> Lazy (InnerError t e)                 -- error to use in case this is the `Bottom` state
    -> (from        : Nat)                   -- start position of token
    -> (till        : Nat)                   -- reverse end position + 1
    -> (now         : Nat)                   -- current position
    -> {auto ix     : Ix (S till) n}         -- end position
    -> {auto 0  lte : LTE from (ixToNat ix)} -- current position
    -> Either (Bounded $ InnerError t e) a
  app dfa state c err from till now =
    let bs := BS from (ixToNat ix)
     in case c of
          Bottom  => Left $ B err (atPos now)
          Ignore  => loop dfa state till
          Parse f => case f (toByteString buf from till) of
            Left  x => Left $ B (Custom x) bs
            Right v => case parser.step (I v state bs) of
              Right s2 => loop (parser.lex s2) s2 till
              Left err => Left err

  inner dfa last start lastPos state 0     cur =
    app dfa state last EOI start lastPos (ixToNat x)
  inner dfa last start lastPos state (S k) cur =
    let arr  := dfa.next `at` cur
        byte := buf `ix` k
     in case arr `atByte` byte of
          FZ => app dfa state last (Byte byte) start lastPos (ixToNat x)
          x  => case dfa.term `at` x of
            Bottom => inner dfa last start lastPos state k x
            i      => inner dfa i    start k       state k x

parseFrom o p pos buf =
  case loop p buf (p.lex p.init) p.init pos of
    Left (B x bs) => Left $ PE o bs (fromIBuffer buf) x
    Right v       => Right v

-- --------------------------------------------------------------------------------
-- -- Streaming run loop
-- --------------------------------------------------------------------------------
--
-- parameters {0 e,c,a  : Type}
--            {0 n      : Nat}
--            (o        : Origin)
--            (lx       : Lexer e c a)
--            (buf      : IBuffer n)
--
--   sinner :
--        (dfa         : DFA e c a)
--     -> (spos        : StreamPos)
--     -> (prev        : ByteString)
--     -> (line        : Nat)
--     -> (col         : Nat)
--     -> (start       : Nat)                  -- start of current token
--     -> (vals        : SnocList $ StreamBounded a) -- accumulated tokens
--     -> (pos         : Nat)                  -- reverse position in the byte array
--     -> {auto x      : Ix pos n}             -- position in the byte array
--     -> {auto 0 lte2 : LTE start (ixToNat x)}
--     -> (cur         : Fin (S dfa.states))       -- current automaton state
--     -> PLexRes e c a
--
--   sloop :
--        (dfa    : DFA e c a)
--     -> (line   : Nat)
--     -> (col    : Nat)
--     -> (vals   : SnocList $ StreamBounded a) -- accumulated tokens
--     -> (pos    : Nat)                  -- reverse position in the byte array
--     -> {auto x : Ix (S pos) n}             -- position in the byte array
--     -> PLexRes e c a
--   sloop dfa l c vals k =
--     case buf `ix` k of
--       10 => case (dfa.next `at` 0) `atByte` 10 of
--         0 => Left (seByte o l c 10)
--         s => sinner dfa (sp o l c) empty (S l) 0 (ixToNat x) vals k s
--       b  => case (dfa.next `at` 0) `atByte` b  of
--         0 => Left (seByte o l c b)
--         s => sinner dfa (sp o l c) empty l (S c) (ixToNat x) vals k s
--
--   sapp :
--        (dfa         : DFA e c a)
--     -> (spos        : StreamPos)
--     -> (prev        : ByteString)
--     -> (line        : Nat)
--     -> (col         : Nat)
--     -> (byte        : Bits8)
--     -> SnocList (StreamBounded a)
--     -> Conv e c a
--     -> (from        : Nat)
--     -> (till        : Nat)
--     -> {auto ix     : Ix (S till) n}
--     -> {auto 0  lte : LTE from (ixToNat ix)}
--     -> PLexRes e c a
--   sapp (D _ next term _) spos prev l c byte sx conv from till =
--    let np := sp o l c
--        bs := SB spos np
--     in case conv of
--          Bottom  => Left (seByte o l c byte)
--          Const cd v => sloop (lx.dfa cd) l c (sx :< B v bs) till
--          Ignore cd  => sloop (lx.dfa cd) l c sx             till
--          Err   x => Left $ SE bs (Custom x)
--          Txt   f => case f (prev <+> toByteString buf from till) of
--            Left  x => Left $ SE bs (Custom x)
--            Right (cd,v) => sloop (lx.dfa cd) l c (sx :< B v bs) till
--
--   sinner dfa spos prev l c start vals 0       cur =
--     Right (LST dfa spos cur (prev <+> toBytes buf start 0) $ sp o l c, vals <>> [])
--   sinner dfa spos prev l c start vals (S k) cur =
--     case ix buf k of
--       10 => case (dfa.next `at` cur) `atByte` 10 of
--         FZ => sapp dfa spos prev l c 10 vals (dfa.term `at` cur) start k
--         st => sinner dfa spos prev (S l) 0 start vals k st
--       b  => case (dfa.next `at` cur) `atByte` b of
--         FZ => sapp dfa spos prev l c b  vals (dfa.term `at` cur) start k
--         st => sinner dfa spos prev l (S c) start vals k st
--
-- plexFrom o lx (LST dfa spos cur prev (SP oe $ P l c)) pos buf =
--   case o == oe of
--     True  => sinner o lx buf dfa spos prev l c 0 [<] pos cur
--     False => sinner o lx buf dfa spos prev 0 0 0 [<] pos cur

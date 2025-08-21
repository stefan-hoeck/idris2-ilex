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
-- Lexer run loop
--------------------------------------------------------------------------------

parameters {0 e,t,a : Type}
           {0 n     : Nat}
           (parser  : Parser Bounds e t a)
           (buf     : IBuffer n)

  inner :
       (dfa         : DFA (Tok e t))         -- current finite automaton
    -> (last        : Maybe $ Tok e t)       -- last encountered terminal state
    -> (start       : Nat)                   -- start of current token
    -> (lastPos     : Nat)                   -- counter for last byte in `last`
    -> {auto y      : Ix (S lastPos) n}      -- end position of `last` in the byte array
    -> (state       : parser.state)          -- accumulated state
    -> (pos         : Nat)                   -- reverse position in the byte array
    -> {auto x      : Ix pos n}              -- position in the byte array
    -> {auto 0 lte1 : LTE start (ixToNat y)}
    -> {auto 0 lte2 : LTE start (ixToNat x)}
    -> (cur         : ByteStep dfa.states $ Tok e t)    -- current automaton state
    -> Either (Bounded $ InnerError t e) a

  -- Tries to create a new token from the current
  -- state and append it to the list of tokens.
  -- We need several pointers into the byte array:
  --   `from` is the start index of the token
  --   `ix`   is the end index of the token (`till` the corresponding reverse index)
  --   `now` is the current position needed in case of
  --   the encountered state being non-terminal
  app :
       (dfa         : DFA (Tok e t))
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
       (dfa    : DFA (Tok e t))                 -- current finite automaton
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

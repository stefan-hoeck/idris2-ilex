module Text.ILex.Runner1

import public Data.ByteString
import public Data.Vect
import public Text.ILex.Parser
import Text.ILex.Internal.Runner

||| Lexing state.
|||
||| This encapsulates the current state as well as
||| the remainder of the previous chunk that marks
||| the beginning of the current token.
public export
record LexState (p : P1 q e a) where
  constructor LST
  {0 sts  : Nat}
  state   : PIx p
  stack   : PST p
  dfa     : PStepper sts p
  cur     : PByteStep sts p
  tok     : Maybe (PStep p)

export
init : (p : P1 q e a) -> F1 q (LexState p)
init p t =
 let stck # t := p.stck t
     L _ dfa  := p.lex `at` p.init
  in LST p.init stck dfa (dfa `at` 0) Nothing # t

||| Result of a partial lexing step: In such a step, we lex
||| till the end of a chunk of bytes, allowing for a remainder of
||| bytes that could not yet be identified as a tokens.
public export
0 PartRes : (p : P1 q e a) -> Type
PartRes p = F1 q (Either e (LexState p, Maybe a))

export
pparseFrom :
     (p      : P1 q e a)
  -> (st     : LexState p)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> PartRes p

export
pparseBytes : (p : P1 q e a) -> LexState p -> ByteString -> PartRes p
pparseBytes p st (BS s $ BV buf off lte) =
  pparseFrom p st s {x = offsetToIx off} (take (off+s) buf)

--------------------------------------------------------------------------------
-- Partial run loop
--------------------------------------------------------------------------------

parameters {0 q,e,a : Type}
           {0 n     : Nat}
           (parser  : P1 q e a)
           (stck    : PST parser)
           (buf     : IBuffer n)
           (bytes   : Ref q ByteString)

  pstep :
       (st          : PIx parser)
    -> (dfa         : PStepper k parser)          -- current finite automaton
    -> (cur         : PByteStep k parser)         -- current automaton state
    -> (prev        : ByteString)
    -> (from        : Ix m n)                     -- start of current token
    -> (pos         : Nat)                        -- reverse position in the byte array
    -> {auto x      : Ix pos n}                   -- position in the byte array
    -> {auto 0 lte2 : LTE (ixToNat from) (ixToNat x)}
    -> PartRes parser

  psucc :
       (st          : PIx parser)
    -> (dfa         : PStepper k parser)          -- current finite automaton
    -> (cur         : PByteStep k parser)         -- current automaton state
    -> (prev        : ByteString)
    -> (last        : PStep parser)               -- last encountered terminal state
    -> (from        : Ix m n)                     -- start of current token
    -> (pos         : Nat)                        -- reverse position in the byte array
    -> {auto x      : Ix pos n}                   -- position in the byte array
    -> {auto 0 lte2 : LTE (ixToNat from) (ixToNat x)}
    -> PartRes parser

  -- Accumulates lexemes by applying the maximum munch strategy:
  -- The largest matched lexeme is consumed and kept.
  -- This consumes at least one byte for the next token and
  -- immediately aborts with an error in case the current
  -- byte leads to the zero state.
  ploop : PIx parser -> (pos : Nat) -> (x : Ix pos n) => PartRes parser
  ploop st 0     t =
   let mv  # t := P1.chunk parser stck t
       L _ dfa := parser.lex `at` st
       _   # t := write1 bytes empty t
    in Right (LST st stck dfa (dfa `at` 0) Nothing, mv) # t
  ploop st (S k) t =
   let L _ dfa := parser.lex `at` st
       cur     := dfa `at` 0
    in case cur `atByte` (buf `ix` k) of
         Done f       => let s2 # t := f (stck # t) in ploop s2 k t
         Move   nxt f => psucc st dfa (dfa `at` nxt) empty f   x k t
         MoveE  nxt   => pstep st dfa (dfa `at` nxt) empty     x k t
         DoneBS f     =>
          let _  # t := writeBS buf x k bytes t
              s2 # t := f (stck # t)
           in ploop s2 k t
         _           =>
          let _  # t := writeBS buf x k bytes t
           in fail parser st stck t

  psucc st dfa cur prev f from 0 t =
   let m # t := P1.chunk parser stck t
       _ # t := writeBSP prev buf from 0 bytes t
    in Right (LST st stck dfa cur $ Just f, m) # t
  psucc st dfa cur prev f from (S k) t =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => psucc st dfa cur prev f from k t
         Done f       => let s2 # t := f (stck # t) in ploop s2 k t
         Move   nxt f => psucc st dfa (dfa `at` nxt) prev f from k t
         MoveE  nxt   => pstep st dfa (dfa `at` nxt) prev   from k t
         DoneBS f     =>
          let _  # t := writeBSP prev buf from k bytes t
              s2 # t := f (stck # t)
           in ploop s2 k t
         Bottom       =>
          let _  # t := writeBSP prev buf from (S k) bytes t
              s2 # t := f (stck # t)
           in ploop s2 (S k) t

  pstep st dfa cur prev from 0 t =
   let m # t := P1.chunk parser stck t
       _ # t := writeBSP prev buf from 0 bytes t
    in Right (LST st stck dfa cur Nothing, m) # t
  pstep st dfa cur prev from (S k) t =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => pstep st dfa cur prev from k t
         Done f       => let s2 # t := f (stck # t) in ploop s2 k t
         Move   nxt f => psucc st dfa (dfa `at` nxt) prev f from k t
         MoveE  nxt   => pstep st dfa (dfa `at` nxt) prev   from k t
         DoneBS f     =>
          let _  # t := writeBSP prev buf from k bytes t
              s2 # t := f (stck # t)
           in ploop s2 k t
         Bottom       =>
          let _  # t := writeBSP prev buf from k bytes t
           in fail parser st stck t

pparseFrom p lst@(LST st sk dfa cur tok) pos buf t =
  case pos of
    0   => Right (lst, Nothing) # t
    S k =>
     let byte     := buf `ix` k
         bytes    := bytes @{p.hasb} sk
         prev # t := read1 bytes t
      in case cur `atByte` byte of
           Keep         => case tok of
             Just f  => psucc p sk buf bytes st dfa cur prev f x k t
             Nothing => pstep p sk buf bytes st dfa cur prev   x k t
           Done   f     => let s2 # t := f (sk # t) in ploop p sk buf bytes s2 k t
           DoneBS f     =>
            let _  # t := writeBSP prev buf x k bytes t
                s2 # t := f (sk # t)
             in ploop p sk buf bytes s2 k t
           Move   nxt f => psucc p sk buf bytes st dfa (dfa `at` nxt) prev f x k t
           MoveE  nxt   => pstep p sk buf bytes st dfa (dfa `at` nxt) prev   x k t
           Bottom     => case tok of
             Just f  => let s2 # t := f (sk # t) in ploop p sk buf bytes s2 (S k) t
             Nothing => fail p st sk t

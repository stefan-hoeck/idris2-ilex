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
record LexState (q,e : Type) (r : Bits32) (s : Type -> Type) where
  constructor LST
  {0 sts  : Nat}
  state   : Index r
  stack   : s q
  dfa     : Stepper sts q r s
  cur     : ByteStep sts q r s
  tok     : Maybe (Tag, Step1 q r s)

export
init : P1 q e r s a -> F1 q (LexState q e r s)
init p t =
 let stck # t := p.stck t
     L _ dfa  := p.lex `at` p.init
  in LST p.init stck dfa (dfa `at` 0) Nothing # t

||| Result of a partial lexing step: In such a step, we lex
||| till the end of a chunk of bytes, allowing for a remainder of
||| bytes that could not yet be identified as a tokens.
public export
0 PartRes : (q,e : Type) -> (r : Bits32) -> (s : Type -> Type) -> (a : Type) -> Type
PartRes q e r s a = F1 q (Either e (LexState q e r s, Maybe a))

export
pparseFrom :
     (p      : P1 q e r s a)
  -> (st     : LexState q e r s)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> PartRes q e r s a

export
pparseBytes : P1 q e r s a -> LexState q e r s -> ByteString -> PartRes q e r s a
pparseBytes p st (BS s $ BV buf off lte) =
  pparseFrom p st s {x = offsetToIx off} (take (off+s) buf)

--------------------------------------------------------------------------------
-- Partial run loop
--------------------------------------------------------------------------------

parameters {0 s     : Type -> Type}
           {0 r     : Bits32}
           {0 q,e,a : Type}
           {0 n     : Nat}
           (stck    : s q)
           (parser  : P1 q e r s a)
           (buf     : IBuffer n)
           (bytes   : Ref q ByteString)

  pstep :
       (st          : Index r)
    -> (dfa         : Stepper k q r s)            -- current finite automaton
    -> (cur         : ByteStep k q r s)           -- current automaton state
    -> (prev        : ByteString)
    -> (from        : Ix m n)                     -- start of current token
    -> (pos         : Nat)                        -- reverse position in the byte array
    -> {auto x      : Ix pos n}                   -- position in the byte array
    -> {auto 0 lte2 : LTE (ixToNat from) (ixToNat x)}
    -> PartRes q e r s a

  psucc :
       (st          : Index r)
    -> (dfa         : Stepper k q r s)            -- current finite automaton
    -> (cur         : ByteStep k q r s)           -- current automaton state
    -> (prev        : ByteString)
    -> (tag         : Tag)
    -> (last        : Step1 q r s)                -- last encountered terminal state
    -> (from        : Ix m n)                     -- start of current token
    -> (pos         : Nat)                        -- reverse position in the byte array
    -> {auto x      : Ix pos n}                   -- position in the byte array
    -> {auto 0 lte2 : LTE (ixToNat from) (ixToNat x)}
    -> PartRes q e r s a

  -- Accumulates lexemes by applying the maximum munch strategy:
  -- The largest matched lexeme is consumed and kept.
  -- This consumes at least one byte for the next token and
  -- immediately aborts with an error in case the current
  -- byte leads to the zero state.
  ploop : Index r -> (pos : Nat) -> (x : Ix pos n) => PartRes q e r s a
  ploop st 0     t =
   let mv  # t := P1.chunk parser stck t
       L _ dfa := parser.lex `at` st
       _   # t := write1 bytes empty t
    in Right (LST st stck dfa (dfa `at` 0) Nothing, mv) # t
  ploop st (S k) t =
   let L _ dfa := parser.lex `at` st
       cur     := dfa `at` 0
    in case cur `atByte` (buf `ix` k) of
         Done tg f    => case tg of
           CONST => let s2 # t := f (stck # t) in ploop s2 k t
           BYTES =>
            let _  # t := writeBS buf x k bytes t
                s2 # t := f (stck # t)
             in ploop s2 k t
         Move   nxt tg f => psucc st dfa (dfa `at` nxt) empty tg f   x k t
         MoveE  nxt      => pstep st dfa (dfa `at` nxt) empty        x k t
         _               =>
          let _  # t := writeBS buf x k bytes t
           in fail parser st stck t

  psucc st dfa cur prev tg f from 0 t =
   let m # t := P1.chunk parser stck t
       _ # t := writeBSP prev buf from 0 bytes t
    in Right (LST st stck dfa cur $ Just (tg,f), m) # t
  psucc st dfa cur prev tg f from (S k) t =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => psucc st dfa cur prev tg f from k t
         Done tg f    => case tg of
           CONST => let s2 # t := f (stck # t) in ploop s2 k t
           BYTES =>
            let _  # t := writeBSP prev buf from k bytes t
                s2 # t := f (stck # t)
             in ploop s2 k t
         Move   nxt tg f => psucc st dfa (dfa `at` nxt) prev tg f from k t
         MoveE  nxt      => pstep st dfa (dfa `at` nxt) prev     from k t
         Bottom          => case tg of
           CONST => let s2 # t := f (stck # t) in ploop s2 (S k) t
           BYTES =>
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
         Done tg f    => case tg of
           CONST => let s2 # t := f (stck # t) in ploop s2 k t
           BYTES =>
            let _  # t := writeBSP prev buf from k bytes t
                s2 # t := f (stck # t)
             in ploop s2 k t
         Move   nxt tg f => psucc st dfa (dfa `at` nxt) prev tg f from k t
         MoveE  nxt      => pstep st dfa (dfa `at` nxt) prev      from k t
         Bottom          =>
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
           Keep          => case tok of
             Just (tg,f) => psucc sk p buf bytes st dfa cur prev tg f x k t
             Nothing => pstep sk p buf bytes st dfa cur prev         x k t
           Done tg f     => case tg of
             CONST => let s2 # t := f (sk # t) in ploop sk p buf bytes s2 k t
             BYTES =>
              let _  # t := writeBSP prev buf x k bytes t
                  s2 # t := f (sk # t)
               in ploop sk p buf bytes s2 k t
           Move   nxt tg f => psucc sk p buf bytes st dfa (dfa `at` nxt) prev tg f x k t
           MoveE  nxt      => pstep sk p buf bytes st dfa (dfa `at` nxt) prev      x k t
           Bottom    => case tok of
             Just (tg,f) => let s2 # t := f (sk # t) in ploop sk p buf bytes s2 (S k) t
             Nothing => fail p st sk t

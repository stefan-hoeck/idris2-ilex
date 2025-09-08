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
  dfa     : Stepper sts (Step q e r s)
  cur     : ByteStep sts (Step q e r s)
  tok     : Step q e r s
  prev    : ByteString

export
init : P1 q e r s a -> F1 q (LexState q e r s)
init p t =
 let stck # t := p.stck t
     L _ dfa  := p.lex `at` p.init
  in LST p.init stck dfa (dfa `at` 0) Err empty # t

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

  psucc :
       (st          : Index r)
    -> (dfa         : Stepper k (Step q e r s))   -- current finite automaton
    -> (cur         : ByteStep k (Step q e r s))  -- current automaton state
    -> (prev        : ByteString)
    -> (last        : Step q e r s)               -- last encountered terminal state
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
    in Right (LST st stck dfa (dfa `at` 0) Err empty, mv) # t
  ploop st (S k) t =
   let L _ dfa := parser.lex `at` st
       cur     := dfa `at` 0
    in case cur `atByte` (buf `ix` k) of
         Done v      => case v of
           Go  f =>
            let s2 # t := f (stck # t)
             in ploop s2 k t
           Rd  f =>
            let s2 # t := f (B stck (toBS buf x k) t)
             in ploop s2 k t
           Err => fail parser st stck (toBS buf x k) t
         Move nxt f => psucc st dfa (dfa `at` nxt) empty f   x k t
         Keep       => psucc st dfa cur            empty Err x k t
         Bottom     => fail parser st stck (toBS buf x k) t

  psucc st dfa cur prev v from 0 t =
   let m # t := P1.chunk parser stck t
    in Right (LST st stck dfa cur v $ toBSP prev buf from 0, m) # t
  psucc st dfa cur prev v from (S k) t =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep       => psucc st dfa cur prev v from k t
         Done v     => case v of
           Go  f =>
            let s2 # t := f (stck # t)
             in ploop s2 k t
           Rd  f =>
            let s2 # t := f (B stck (toBSP prev buf from k) t)
             in ploop s2 k t
           Err => fail parser st stck (toBSP prev buf from k) t
         Move nxt f => psucc st dfa (dfa `at` nxt) prev f from k t
         Bottom     => case v of
           Go  f =>
            let s2 # t := f (stck # t)
             in ploop s2 (S k) t
           Rd  f =>
            let s2 # t := f (B stck (toBSP prev buf from (S k)) t)
             in ploop s2 (S k) t
           Err => fail parser st stck (toBSP prev buf from k) t

pparseFrom p lst@(LST st sk dfa cur tok prev) pos buf t =
  case pos of
    0   => Right (lst, Nothing) # t
    S k =>
     let byte := buf `ix` k
      in case cur `atByte` byte of
           Keep     => psucc sk p buf st dfa cur prev tok x k t
           Done v   => case v of
             Go  f =>
              let s2 # t := f (sk # t)
               in ploop sk p buf s2 k t
             Rd  f =>
              let s2 # t := f (B sk (toBSP prev buf x k) t)
               in ploop sk p buf s2 k t
             Err => fail p st sk (toBSP prev buf x k) t
           Move nxt f => psucc sk p buf st dfa (dfa `at` nxt) prev f x k t
           Bottom     => case tok of
             Go  f =>
              let s2 # t := f (sk # t)
               in ploop sk p buf s2 (S k) t
             Rd  f =>
              let s2 # t := f (B sk prev t)
               in ploop sk p buf s2 (S k) t
             Err => fail p st sk prev t

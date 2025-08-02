module Text.ILex.Runner1

import public Data.ByteString
import public Data.Linear.Token
import public Data.Vect
import public Text.ILex.Bounds
import public Text.ILex.Error
import public Text.ILex.FC
import public Text.ILex.Lexer

import Data.Linear.ELift1
import Data.Linear.Ref1
import Data.Buffer
import Data.Buffer.Core
import Data.Buffer.Indexed
import Text.ILex.Internal.Runner

record DBStep e t where
  constructor DBS
  dfa : DFA e t
  cur : ByteStep dfa.states e t

||| Lexing state.
|||
||| This encapsulates the current state as well as
||| the remainder of the previous chunk that marks
||| the beginning of the current token.
export
record LexState1 (q,e,s,t : Type) where
  constructor LST1
  state : Ref q s
  cur   : Ref q (DBStep e t)
  start : Ref q StreamPos
  tok   : Ref q (Maybe (Tok e t))
  prev  : Ref q (ByteString)
  org   : Ref q Origin
  line  : Ref q Nat
  col   : Ref q Nat

export
init1 : Origin -> (p : Parser b e t a) -> F1 q (LexState1 q e p.state t)
init1 o p t =
 let dfa       := p.lex p.init
     state # t := ref1 p.init t
     cur   # t := ref1 (DBS dfa (dfa.next `at` 0)) t
     start # t := ref1 (SP o $ P 0 0) t
     tok   # t := ref1 Nothing t
     prev  # t := ref1 ByteString.empty t
     org   # t := ref1 o t
     line  # t := ref1 Z t
     col   # t := ref1 Z t
  in LST1 state cur start tok prev org line col # t

inc1 : Bits8 -> LexState1 q e s t -> F1' q
inc1 10 lst1 t =
 let l # t := read1 lst1.line t
     _ # t := write1 lst1.line (S l) t
  in write1 lst1.col 0 t
inc1 _  lst1 t =
 let c # t := read1 lst1.col t
  in write1 lst1.col (S c) t

||| Result of a partial lexing step: In such a step, we lex
||| till the end of a chunk of bytes, allowing for a remainder of
||| bytes that could not yet be identified as a tokens.
public export
0 PLexRes1 : (q,e,s,t,a : Type) -> Type
PLexRes1 q e s t a = E1 q [StreamError t e] (Maybe a)

curPos : LexState1 q e s t -> F1 q StreamPos
curPos lst1 t =
 let o # t := read1 lst1.org t
     l # t := read1 lst1.line t
     c # t := read1 lst1.col t
  in sp o l c # t

failByte : Bits8 -> LexState1 q e s t -> PLexRes1 q e s t a
failByte b lst1 t =
 let sp # t := curPos lst1 t
  in fail1 (B (Byte b) (SB sp sp)) t

setOrigin : Origin -> LexState1 q e s t -> F1' q
setOrigin o lst1 t =
 let oe # t := read1 lst1.org t
  in case o == oe of
       False =>
        let _ # t := write1 lst1.org  o t
            _ # t := write1 lst1.line 0 t
         in write1 lst1.col 0 t
       True  => () # t

plexFrom :
     (o      : Origin)
  -> (p      : Parser StreamBounds e t a)
  -> (st     : LexState1 q e p.state t)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> PLexRes1 q e p.state t a

export %inline
pparseBytes1 :
     {auto lft : ELift1 q f}
  -> {auto has : Has (StreamError t e) es}
  -> (p : Parser StreamBounds e t a)
  -> Origin
  -> LexState1 q e p.state t
  -> ByteString
  -> f es (Maybe a)
pparseBytes1 l o st (BS s $ BV buf off lte) =
  elift1 $ \t =>
    case plexFrom o l st s {x = offsetToIx off} (take (off+s) buf) t of
      R x t        => R x t
      E (Here x) t => throw1 x t

parameters {0 q,e,t,a : Type}
           {0 n       : Nat}
           (parser    : Parser StreamBounds e t a)
           (buf       : IBuffer n)
           (lst1      : LexState1 q e parser.state t)

  stop :
       (dfa : DFA e t)
    -> (cur : ByteStep dfa.states e t)
    -> (rem : ByteString)
    -> PLexRes1 q e parser.state t a
  stop dfa cur rem t =
   let st     # t := read1 lst1.state t
       (s2,m)     := parser.chunk st
       prev   # t := read1 lst1.prev t
       _      # t := write1 lst1.prev (prev <+> rem) t
       _      # t := write1 lst1.state s2 t
       _      # t := write1 lst1.cur (DBS dfa cur) t
    in R m t

  covering
  sinner :
       (dfa         : DFA e t)
    -> (start       : Nat)                     -- start of current token
    -> (pos         : Nat)                     -- reverse position in the byte array
    -> {auto x      : Ix pos n}                -- position in the byte array
    -> {auto xt     : Ix (S pos) n}            -- position in the byte array
    -> {auto 0 lte1 : LTE start (ixToNat xt)}
    -> {auto 0 lte2 : LTE start (ixToNat x)}
    -> (cur         : ByteStep dfa.states e t) -- current automaton state
    -> PLexRes1 q e parser.state t a

  covering %inline
  sloop :
       (dfa    : DFA e t)
    -> (pos    : Nat)                  -- reverse position in the byte array
    -> {auto x : Ix pos n}             -- position in the byte array
    -> (cur    : ByteStep dfa.states e t) -- current automaton state
    -> PLexRes1 q e parser.state t a

  covering
  sapp0 :
       (dfa         : DFA e t)
    -> Tok e t
    -> (pos         : Nat)
    -> {auto ix     : Ix pos n}
    -> PLexRes1 q e parser.state t a
  sapp0 dfa tok pos t =
   let start # t := read1 lst1.start t
       np    # t := curPos lst1 t
       bs        := SB start np
       state # t := read1 lst1.state t
       prev  # t := read1 lst1.prev t
       _     # t := write1 lst1.prev empty t
       _     # t := write1 lst1.tok Nothing t
       _     # t := write1 lst1.start np t
    in case tok of
         Ignore  => sloop dfa pos (dfa.next `at` 0) t
         Const v => case parser.step (I v state bs) of
           Right s2 =>
            let dfa2  := parser.lex s2
                cur   := dfa2.next `at` 0
                _ # t := write1 lst1.state s2 t
             in sloop dfa2 pos cur t
           Left err => fail1 err t
         Parse f => case f prev of
           Left  x => fail1 (B (Custom x) bs) t
           Right v => case parser.step (I v state bs) of
             Right s2 =>
              let dfa2  := parser.lex s2
                  cur   := dfa2.next `at` 0
                  _ # t := write1 lst1.state s2 t
               in sloop dfa2 pos cur t
             Left err => fail1 err t

  covering
  sapp :
       (dfa         : DFA e t)
    -> Tok e t
    -> (from        : Nat)
    -> (till        : Nat)
    -> {auto ix     : Ix (S till) n}
    -> {auto 0  lte : LTE from (ixToNat ix)}
    -> PLexRes1 q e parser.state t a
  sapp dfa tok from till t =
   let start # t := read1 lst1.start t
       np    # t := curPos lst1 t
       bs        := SB start np
       state # t := read1 lst1.state t
       prev  # t := read1 lst1.prev t
       _     # t := write1 lst1.prev empty t
       _     # t := write1 lst1.tok Nothing t
       _     # t := write1 lst1.start np t
    in case tok of
         Ignore  => sloop dfa till (dfa.next `at` 0) t
         Const v => case parser.step (I v state bs) of
           Right s2 =>
            let dfa2  := parser.lex s2
                cur   := dfa2.next `at` 0
                _ # t := write1 lst1.state s2 t
             in sloop dfa2 till cur t
           Left err => fail1 err t
         Parse f => case f (prev <+> toByteString buf from till) of
           Left  x => fail1 (B (Custom x) bs) t
           Right v => case parser.step (I v state bs) of
             Right s2 =>
              let dfa2  := parser.lex s2
                  cur   := dfa2.next `at` 0
                  _ # t := write1 lst1.state s2 t
               in sloop dfa2 till cur t
             Left err => fail1 err t

  sinner dfa start 0     cur t = stop dfa cur (toBytes buf start 0) t
  sinner dfa start (S k) cur t =
   let b   := ix buf k
    in case cur `atByte` b of
         KeepT        =>
          let _ # t := inc1 b lst1 t
           in sinner dfa start k cur t
         Done tok     =>
          let _ # t := inc1 b lst1 t
           in sapp dfa tok start k t
         Keep         =>
          let _ # t := inc1 b lst1 t
              _ # t := write1 lst1.tok Nothing t
           in sinner dfa start k cur t
         Move st      =>
          let _ # t := inc1 b lst1 t
              _ # t := write1 lst1.tok Nothing t
           in sinner dfa start k (dfa.next `at` st) t
         MoveT st tok =>
          let _ # t := inc1 b lst1 t
              _ # t := write1 lst1.tok (Just tok) t
           in sinner dfa start k (dfa.next `at` st) t
         Bottom       => case read1 lst1.tok t of
           Just v  # t => sapp dfa v start (S k) t
           Nothing # t => failByte b lst1 t

  sloop dfa 0     cur t = stop dfa cur empty t
  sloop dfa (S k) cur t =
   let b     := ix buf k
    in case cur `atByte` b of
         KeepT        =>
          let _ # t := inc1 b lst1 t
           in sinner dfa (ixToNat x) k cur t
         Done tok     =>
          let _ # t := inc1 b lst1 t
           in sapp dfa tok (ixToNat x) k t
         Keep         =>
          let _ # t := inc1 b lst1 t
              _ # t := write1 lst1.tok Nothing t
           in sinner dfa (ixToNat x) k cur t
         Move st      =>
          let _ # t := inc1 b lst1 t
              _ # t := write1 lst1.tok Nothing t
           in sinner dfa (ixToNat x) k (dfa.next `at` st) t
         MoveT st tok =>
          let _ # t := inc1 b lst1 t
              _ # t := write1 lst1.tok (Just tok) t
           in sinner dfa (ixToNat x) k (dfa.next `at` st) t
         Bottom       => case read1 lst1.tok t of
           Just v  # t => sapp0 dfa v (S k) t
           Nothing # t => failByte b lst1 t

plexFrom o lx lst1 pos buf t =
  assert_total $
   let _  # t := setOrigin o lst1 t
       v  # t := read1 lst1.cur t
    in assert_total $ sloop lx buf lst1 v.dfa pos v.cur t

export
appLast1 :
     {auto lft : ELift1 q f}
  -> {auto has : Has (StreamError t e) es}
  -> (parser : Parser StreamBounds e t a)
  -> (lst1   : LexState1 q e parser.state t)
  -> f es a
appLast1 parser lst1 =
  elift1 $ \t =>
   let start # t := read1 lst1.start t
       end   # t := curPos lst1 t
       cur   # t := read1 lst1.cur t
       state # t := read1 lst1.state t
       tok   # t := read1 lst1.tok t
       prev  # t := read1 lst1.prev t
    in case appLast parser start end cur.dfa tok state prev of
         Right v => R v t
         Left  x => throw1 x t

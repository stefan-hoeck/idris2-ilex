module Text.ILex.Runner1

import public Data.ByteString
import public Data.Linear.Token
import public Data.Vect
import public Text.ILex.Bounds
import public Text.ILex.Error
import public Text.ILex.FC
import public Text.ILex.Lexer

import Data.Linear.ELift1
import Data.Array.All
import Data.Buffer
import Data.Buffer.Core
import Data.Buffer.Mutable
import Text.ILex.Internal.Runner

record DBStep e t where
  constructor DBS
  dfa : DFA e t
  cur : ByteStep dfa.states e t

public export
0 LexTypes : (e,s,t : Type) -> List Type
LexTypes e s t =
  [ s
  , DBStep e t
  , StreamPos
  , Maybe (Tok e t)
  , ByteString
  , Origin
  , Nat
  , Nat
  ]

||| Lexing state.
|||
||| This encapsulates the current state as well as
||| the remainder of the previous chunk that marks
||| the beginning of the current token.
public export
0 LexState1 : (q,e,s,t : Type) -> Type
LexState1 q e s t = MHArr q (LexTypes e s t)

State, Cur, Pos, Tok, Prev, Org, Line, Col : Fin 8
State = 0
Cur   = 1
Pos   = 2
Tok   = 3
Prev  = 4
Org   = 5
Line  = 6
Col   = 7

export
init1 : Origin -> (p : Parser b e t a) -> F1 q (LexState1 q e p.state t)
init1 o p t =
 let dfa := p.lex p.init
     cur := DBS dfa (dfa.next `at` 0)
  in mall1 [p.init, cur, (SP o $ P 0 0), Nothing, empty, o, 0, 0] t

inc1 : Bits8 -> LexState1 q e s t -> F1' q
inc1 10 lst1 t =
 let l # t := All.get lst1 Line t
     _ # t := All.set lst1 Line (S l) t
  in All.set lst1 Col 0 t
inc1 _  lst1 t =
 let c # t := All.get lst1 Col t
  in All.set lst1 Col (S c) t

||| Result of a partial lexing step: In such a step, we lex
||| till the end of a chunk of bytes, allowing for a remainder of
||| bytes that could not yet be identified as a tokens.
public export
0 PLexRes1 : (q,e,s,t,a : Type) -> Type
PLexRes1 q e s t a = E1 q [StreamError t e] (Maybe a)

curPos : LexState1 q e s t -> F1 q StreamPos
curPos lst1 t =
 let o # t := All.get lst1 Org t
     l # t := All.get lst1 Line t
     c # t := All.get lst1 Col t
  in sp o l c # t

failByte : Bits8 -> LexState1 q e s t -> PLexRes1 q e s t a
failByte b lst1 t =
 let sp # t := curPos lst1 t
  in fail1 (B (Byte b) (SB sp sp)) t

setOrigin : Origin -> LexState1 q e s t -> F1' q
setOrigin o lst1 t =
 let oe # t := All.get lst1 Org t
  in case o == oe of
       False =>
        let _ # t := All.set lst1 Org o t
            _ # t := All.set lst1 Line 0 t
         in All.set lst1 Col 0 t
       True  => () # t

plexFrom :
     (o      : Origin)
  -> (p      : Parser StreamBounds e t a)
  -> (st     : LexState1 q e p.state t)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> MBuffer q n
  -> PLexRes1 q e p.state t a

export %inline
pparseBytes1 :
     {auto lft : ELift1 q f}
  -> {auto has : Has (StreamError t e) es}
  -> (p : Parser StreamBounds e t a)
  -> Origin
  -> LexState1 q e p.state t
  -> (n ** MBuffer q n)
  -> f es (Maybe a)
pparseBytes1 l o st (n ** buf) =
  elift1 $ \t =>
    case plexFrom o l st n buf t of
      R x t        => R x t
      E (Here x) t => throw1 x t

export
toBS1 :
     MBuffer q n
  -> (from        : Nat)
  -> (0    till   : Nat)
  -> {auto ix     : Ix (S till) n}
  -> {auto 0  lte : LTE from (ixToNat ix)}
  -> F1 q ByteString
toBS1 buf from till t =
  let ib # t := bufSubstringFromTo buf from (ixToNat ix) {lt = ixLT ix} t
   in BS _ (fromIBuffer ib) # t

export
toBytes1 :
     MBuffer q n
  -> (from        : Nat)
  -> (0    to     : Nat)
  -> {auto ix     : Ix to n}
  -> {auto 0  lte : LTE from (ixToNat ix)}
  -> F1 q ByteString
toBytes1 buf from to t =
 let ib # t := bufSubstringFromTill buf from (ixToNat ix) {lt2 = ixLTE ix} t
  in BS _ (fromIBuffer ib) # t

parameters {0 q,e,t,a : Type}
           {0 n       : Nat}
           (parser    : Parser StreamBounds e t a)
           (buf       : MBuffer q n)
           (lst1      : LexState1 q e parser.state t)

  stop :
       (dfa : DFA e t)
    -> (cur : ByteStep dfa.states e t)
    -> (rem : ByteString)
    -> PLexRes1 q e parser.state t a
  stop dfa cur rem t =
   let st     # t := All.get lst1 State t
       (s2,m)     := parser.chunk st
       prev   # t := All.get lst1 Prev t
       _      # t := All.set lst1 Prev (prev <+> rem) t
       _      # t := All.set lst1 State s2 t
       _      # t := All.set lst1 Cur (DBS dfa cur) t
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
   let start # t := All.get lst1 Pos t
       np    # t := curPos lst1 t
       bs        := SB start np
       state # t := All.get lst1 State t
       prev  # t := All.get lst1 Prev t
       _     # t := All.set lst1 Prev empty t
       _     # t := All.set lst1 Tok Nothing t
       _     # t := All.set lst1 Pos np t
    in case tok of
         Ignore  => sloop dfa pos (dfa.next `at` 0) t
         Const v => case parser.step (I v state bs) of
           Right s2 =>
            let dfa2  := parser.lex s2
                cur   := dfa2.next `at` 0
                _ # t := All.setElem lst1 s2 t
             in sloop dfa2 pos cur t
           Left err => fail1 err t
         Parse f => case f prev of
           Left  x => fail1 (B (Custom x) bs) t
           Right v => case parser.step (I v state bs) of
             Right s2 =>
              let dfa2  := parser.lex s2
                  cur   := dfa2.next `at` 0
                  _ # t := All.setElem lst1 s2 t
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
   let start # t := All.get lst1 Pos t
       np    # t := curPos lst1 t
       bs        := SB start np
       state # t := All.get lst1 State t
       prev  # t := All.get lst1 Prev t
       _     # t := All.set lst1 Prev empty t
       _     # t := All.set lst1 Tok Nothing t
       _     # t := All.set lst1 Pos np t
    in case tok of
         Ignore  => sloop dfa till (dfa.next `at` 0) t
         Const v => case parser.step (I v state bs) of
           Right s2 =>
            let dfa2  := parser.lex s2
                cur   := dfa2.next `at` 0
                _ # t := All.set lst1 State s2 t
             in sloop dfa2 till cur t
           Left err => fail1 err t
         Parse f =>
          let bytes # t := toBS1 buf from till t
           in case f (prev <+> bytes) of
                Left  x => fail1 (B (Custom x) bs) t
                Right v => case parser.step (I v state bs) of
                  Right s2 =>
                   let dfa2  := parser.lex s2
                       cur   := dfa2.next `at` 0
                       _ # t := All.set lst1 State s2 t
                    in sloop dfa2 till cur t
                  Left err => fail1 err t

  sinner dfa start 0     cur t =
   let bytes # t := toBytes1 buf start 0 t
    in stop dfa cur bytes t
  sinner dfa start (S k) cur t =
   let b # t := getIx buf k t
    in case cur `atByte` b of
         KeepT        =>
          let _ # t := inc1 b lst1 t
           in sinner dfa start k cur t
         Done tok     =>
          let _ # t := inc1 b lst1 t
           in sapp dfa tok start k t
         Keep         =>
          let _ # t := inc1 b lst1 t
              _ # t := All.set lst1 Tok Nothing t
           in sinner dfa start k cur t
         Move st      =>
          let _ # t := inc1 b lst1 t
              _ # t := All.set lst1 Tok Nothing t
           in sinner dfa start k (dfa.next `at` st) t
         MoveT st tok =>
          let _ # t := inc1 b lst1 t
              _ # t := All.set lst1 Tok (Just tok) t
           in sinner dfa start k (dfa.next `at` st) t
         Bottom       => case All.get lst1 Tok t of
           Just v  # t => sapp dfa v start (S k) t
           Nothing # t => failByte b lst1 t

  sloop dfa 0     cur t = stop dfa cur empty t
  sloop dfa (S k) cur t =
   let b # t := getIx buf k t
    in case cur `atByte` b of
         KeepT        =>
          let _ # t := inc1 b lst1 t
           in sinner dfa (ixToNat x) k cur t
         Done tok     =>
          let _ # t := inc1 b lst1 t
           in sapp dfa tok (ixToNat x) k t
         Keep         =>
          let _ # t := inc1 b lst1 t
              _ # t := All.set lst1 Tok Nothing t
           in sinner dfa (ixToNat x) k cur t
         Move st      =>
          let _ # t := inc1 b lst1 t
              _ # t := All.set lst1 Tok Nothing t
           in sinner dfa (ixToNat x) k (dfa.next `at` st) t
         MoveT st tok =>
          let _ # t := inc1 b lst1 t
              _ # t := All.set lst1 Tok (Just tok) t
           in sinner dfa (ixToNat x) k (dfa.next `at` st) t
         Bottom       => case All.get lst1 Tok t of
           Just v  # t => sapp0 dfa v (S k) t
           Nothing # t => failByte b lst1 t

plexFrom o lx lst1 pos buf t =
  assert_total $
   let _  # t := setOrigin o lst1 t
       v  # t := All.get lst1 Cur t
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
   let start # t := All.get lst1 Pos t
       end   # t := curPos lst1 t
       cur   # t := All.get lst1 Cur t
       state # t := All.get lst1 State t
       tok   # t := All.get lst1 Tok t
       prev  # t := All.get lst1 Prev t
    in case appLast parser start end cur.dfa tok state prev of
         Right v => R v t
         Left  x => throw1 x t

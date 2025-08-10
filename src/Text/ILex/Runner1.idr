module Text.ILex.Runner1

import public Data.ByteString
import public Data.Linear.Token
import public Data.Vect
import public Text.ILex.Bounds
import public Text.ILex.Error
import public Text.ILex.FC
import public Text.ILex.Lexer
import public Text.ILex.Runner

import Data.Linear.ELift1
import Data.Buffer
import Data.Buffer.Core
import Data.Buffer.Mutable
import Text.ILex.Internal.Runner

||| Result of a partial lexing step: In such a step, we lex
||| till the end of a chunk of bytes, allowing for a remainder of
||| bytes that could not yet be identified as a tokens.
public export
0 PLexRes1 : (q,e,s,t,a : Type) -> Type
PLexRes1 q e s t a = E1 q [StreamError t e] (LexState e s t, Maybe a)

plexFrom :
     (o      : Origin)
  -> (p      : Parser StreamBounds e t a)
  -> (st     : LexState e p.state t)
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
  -> LexState e p.state t
  -> (n ** MBuffer q n)
  -> f es (LexState e p.state t, Maybe a)
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
  -> (prev        : ByteString)
  -> {auto ix     : Ix (S till) n}
  -> {auto 0  lte : LTE from (ixToNat ix)}
  -> F1 q ByteString
toBS1 buf from till (BS 0 _) t =
  let ib # t := bufSubstringFromTo buf from (ixToNat ix) {lt = ixLT ix} t
   in BS _ (fromIBuffer ib)# t
toBS1 buf from till prev t =
  let ib # t := bufSubstringFromTo buf from (ixToNat ix) {lt = ixLT ix} t
   in (prev <+> BS _ (fromIBuffer ib)) # t

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

export %inline
toStr1 :
     MBuffer q n
  -> (from        : Nat)
  -> (0    till   : Nat)
  -> (prev        : ByteString)
  -> {auto ix     : Ix (S till) n}
  -> {auto 0  lte : LTE from (ixToNat ix)}
  -> F1 q String
toStr1 buf from till prev t =
 let s2 # t := bufStringFromTo buf from (ixToNat ix) {lt = ixLT ix} t
  in case prev.size of
       0 => s2 # t
       _ => (toString prev ++ s2) # t

%inline
nextLine : Bits8 -> Nat -> Nat
nextLine 10 = S
nextLine _  = id

%inline
nextCol : Bits8 -> Nat -> Nat
nextCol 10 _ = 0
nextCol _  n = S n

parameters {0 q,e,t,a : Type}
           {0 n       : Nat}
           (o         : Origin)
           (parser    : Parser StreamBounds e t a)
           (buf       : MBuffer q n)

  covering
  sinner :
       (dfa         : DFA e t)
    -> (spos        : StreamPos)
    -> (tok         : Maybe (Tok e t))
    -> (prev        : ByteString)
    -> (line,col    : Nat)
    -> (start       : Nat)                     -- start of current token
    -> (state       : parser.state)            -- accumulated tokens
    -> (pos         : Nat)                     -- reverse position in the byte array
    -> {auto x      : Ix pos n}                -- position in the byte array
    -> {auto xt     : Ix (S pos) n}           -- position in the byte array
    -> {auto 0 lte1 : LTE start (ixToNat xt)}
    -> {auto 0 lte2 : LTE start (ixToNat x)}
    -> (cur         : ByteStep dfa.states e t) -- current automaton state
    -> PLexRes1 q  e parser.state t a

  covering
  sloop :
       (dfa      : DFA e t)
    -> (spos     : StreamPos)
    -> (tok      : Maybe (Tok e t))
    -> (prev     : ByteString)
    -> (line,col : Nat)
    -> (state    : parser.state)         -- accumulated tokens
    -> (pos      : Nat)                  -- reverse position in the byte array
    -> {auto x   : Ix pos n}             -- position in the byte array
    -> (cur      : ByteStep dfa.states e t) -- current automaton state
    -> PLexRes1 q e parser.state t a

  covering
  sapp0 :
       (dfa         : DFA e t)
    -> (spos        : StreamPos)
    -> (prev        : ByteString)
    -> (line,col    : Nat)
    -> parser.state
    -> Tok e t
    -> (pos         : Nat)
    -> {auto ix     : Ix pos n}
    -> PLexRes1 q e parser.state t a
  sapp0 dfa spos prev line col state conv pos t =
   let np := sp o line col
       bs := SB spos np
    in case conv of
         Ignore  => sloop dfa np Nothing empty line col state pos (dfa.next `at` 0) t
         Const v => case parser.step (I v state bs) of
           Right s2 =>
            let dfa2 := parser.lex s2
                cur  := dfa2.next `at` 0
             in sloop dfa2 np Nothing empty line col s2 pos cur t
           Left err => fail1 err t
         Txt f => case f (toString prev) of
           Left  x => fail1 (B (Custom x) bs) t
           Right v => case parser.step (I v state bs) of
             Right s2 =>
              let dfa2 := parser.lex s2
                  cur  := dfa2.next `at` 0
               in sloop dfa2 np Nothing empty line col s2 pos cur t
             Left err => fail1 err t
         Bytes f => case f prev of
           Left  x => fail1 (B (Custom x) bs) t
           Right v => case parser.step (I v state bs) of
             Right s2 =>
              let dfa2 := parser.lex s2
                  cur  := dfa2.next `at` 0
               in sloop dfa2 np Nothing empty line col s2 pos cur t
             Left err => fail1 err t

  covering
  sapp :
       (dfa         : DFA e t)
    -> (spos        : StreamPos)
    -> (prev        : ByteString)
    -> (line,col    : Nat)
    -> parser.state
    -> Tok e t
    -> (from        : Nat)
    -> (till        : Nat)
    -> {auto ix     : Ix (S till) n}
    -> {auto 0  lte : LTE from (ixToNat ix)}
    -> PLexRes1 q e parser.state t a
  sapp dfa spos prev line col state conv from till t =
   let np := SP o (P line col)
       bs := SB spos np
    in case conv of
         Ignore  => sloop dfa np Nothing empty line col state till (dfa.next `at` 0) t
         Const v => case parser.step (I v state bs) of
           Right s2 =>
            let dfa2 := parser.lex s2
                cur  := dfa2.next `at` 0
             in sloop dfa2 np Nothing empty line col s2 till cur t
           Left err => fail1 err t
         Txt f =>
          let str # t  := toStr1 buf from till prev t
              Right v  := f str         | Left x => fail1 (B (Custom x) bs) t
              i        := I v state bs
              Right s2 := parser.step i | Left x => fail1 x t
              dfa2     := parser.lex s2
              cur      := dfa2.next `at` 0
           in sloop dfa2 np Nothing empty line col s2 till cur t
         Bytes f =>
          let bts # t  := toBS1 buf from till prev t
              Right v  := f bts         | Left x => fail1 (B (Custom x) bs) t
              i        := I v state bs
              Right s2 := parser.step i | Left x => fail1 x t
              dfa2     := parser.lex s2
              cur      := dfa2.next `at` 0
           in sloop dfa2 np Nothing empty line col s2 till cur t

  sinner dfa spos tok prev line col start state 0     cur t =
    let (s2,m) := parser.chunk state
        bs # t := toBytes1 buf start 0 t
        bytes  := prev <+> bs
     in R (LST s2 dfa spos cur tok bytes $ sp o line col, m) t
  sinner dfa spos tok prev line col start state (S k) cur t =
   let b # t := getIx buf k t
       l2    := nextLine b line
       c2    := nextCol b col
    in case cur `atByte` b of
         KeepT        => sinner dfa spos tok        prev l2 c2 start state k cur t
         Done tok     => sapp dfa spos prev l2 c2 state tok start k t
         Keep         => sinner dfa spos Nothing    prev l2 c2 start state k cur t
         Move st      => sinner dfa spos Nothing    prev l2 c2 start state k (dfa.next `at` st) t
         MoveT st tok => sinner dfa spos (Just tok) prev l2 c2 start state k (dfa.next `at` st) t
         Bottom       => case tok of
           Nothing => fail1 (seByte o (P line col) b) t
           Just v  => sapp dfa spos prev line col state v start (S k) t

  sloop dfa spos tok prev line col state 0       cur t =
    let (s2,m) := parser.chunk state
     in R (LST s2 dfa spos cur tok prev $ sp o line col, m) t
  sloop dfa spos tok prev line col state (S k) cur t =
   let b # t := getIx buf k t
       l2    := nextLine b line
       c2    := nextCol b col
    in case cur `atByte` b of
        KeepT        => sinner dfa spos tok        prev l2 c2 (ixToNat x) state k cur t
        Done tok     => sapp dfa spos prev l2 c2 state tok (ixToNat x) k t
        Keep         => sinner dfa spos Nothing    prev l2 c2 (ixToNat x) state k cur t
        Move st      => sinner dfa spos Nothing    prev l2 c2 (ixToNat x) state k (dfa.next `at` st) t
        MoveT st tok => sinner dfa spos (Just tok) prev l2 c2 (ixToNat x) state k (dfa.next `at` st) t
        Bottom       => case tok of
          Just v  => sapp0 dfa spos prev line col state v (S k) t
          Nothing => fail1 (seByte o (P line col) b) t

plexFrom o lx (LST st dfa spos cur tok prev (SP oe (P l c))) pos buf t =
  assert_total $ case o == oe of
    True  => sloop o lx buf dfa spos tok prev l c st pos cur t
    False => sloop o lx buf dfa spos tok prev 0 0 st pos cur t

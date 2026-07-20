module Text.ILex.Parser

import Derive.Prelude
import Data.Buffer
import Syntax.T1
import public Data.Prim.Bits32
import public Data.ByteString
import public Data.Linear.Ref1
import public Text.ByteBounds
import public Text.ParseError
import public Text.ILex.RExp
import public Text.ILex.Lexer

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "scheme:(lambda (x i) (make-vector x i))"
         "javascript:lambda:(i,x,w) => Array(i).fill(x)"
prim__newMachine : Bits32 -> AnyPtr -> PrimIO AnyPtr

%foreign "scheme:(lambda (x i) (vector-ref x i))"
         "javascript:lambda:(x,bi) => x[bi]"
prim__machineGet : AnyPtr -> Bits32 -> AnyPtr

%foreign "scheme:(lambda (x i w) (vector-set! x i w))"
         "javascript:lambda:(x,i,w) => {x[i] = w}"
prim__machineSet : AnyPtr -> Bits32 -> (val : AnyPtr) -> PrimIO ()

export
record Arr32 (n : Bits32) (a : Type) where
  constructor A32
  ptr : AnyPtr

export %inline
at : Arr32 n a -> Index n -> a
at (A32 p) x = believe_me $ prim__machineGet p x.val

public export
record Entry (n : Bits32) (a : Type) where
  constructor E
  index : Index n
  value : a

export %inline
entry : Cast t (Index n) => t -> a -> Entry n a
entry x v = E (cast x) v

export
arr32 : (n : Bits32) -> (dflt : a) -> List (Entry n a) -> Arr32 n a
arr32 n dflt es =
  run1 $ \t =>
   let p # t := ffi (prim__newMachine n (believe_me dflt)) t
    in fill es p t

  where
    fill : List (Entry n a) -> AnyPtr -> F1 x (Arr32 n a)
    fill []             p t = A32 p # t
    fill (E x d :: xs) p t =
     let _ # t := ffi (prim__machineSet p x.val (believe_me d)) t
      in fill xs p t

public export
0 Lex1 : (q : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
Lex1 q r s = Arr32 r (DFA q r s)

--------------------------------------------------------------------------------
-- HasBytes Interface
--------------------------------------------------------------------------------

public export
record RelBounds (n : Nat) where
  constructor RB
  from        : Nat
  till        : Nat
  {auto 0 lt1 : LTE from till}
  {auto 0 lt2 : LTE till n}

export %inline
initial : (0 n : Nat) -> RelBounds n
initial n = RB 0 0

export %inline
final : (n : Nat) -> RelBounds n
final n = RB n n

export %inline
fromTill :
     (0 from, till : Nat)
  -> {auto fromIx : Ix from n}
  -> {auto tillIx : Ix till n}
  -> {auto 0 prf  : LTE (ixToNat fromIx) (ixToNat tillIx)}
  -> RelBounds n
fromTill from till = RB (ixToNat fromIx) (ixToNat tillIx) {lt2 = ixLTE _}

export %inline
bytesFromTill :
     IBuffer n
  -> (from       : Nat)
  -> (till       : Nat)
  -> {auto 0 lt1 : LTE from n}
  -> {auto 0 lt2 : LTE till n}
  -> ByteString
bytesFromTill buf from till =
  BS (till `minus` from) (BV buf from $ transitive (plusMinusLTE _ _ lt1) lt2)

-- ||| An interface for mutable parser stacks `s` that facilitates
-- ||| parsing string tokens containing escape sequences.
-- public export
-- interface HasBytes (0 s : Type -> Type) where
--   constructor MkHB
--   copy :
--        (size, offset : Nat)
--     -> ByteString
--     -> IBuffer size
--     -> Ref q (RelBounds size)
--     -> s q
--     -> s q
--
--   bufSize   : s q -> Nat
--
--   ||| Returns the remainder of the previous bytestring that should
--   ||| be used as the beginning of the current token.
--   prev      : s q -> ByteString
--
--   ||| The byte vector currently being processed.
--   cur       : (v : s q) -> IBuffer (bufSize v)
--
--   ||| Absolute position of the first byte of `prev`.
--   prevOffset    : s q -> Nat
--
--   ||| Absolute position of the first byte of `cur`
--   ||| (this equals `prevOffset + prev.size` but should be
--   ||| provided as a separate field for reasons of efficiency)
--   curOffset    : s q -> Nat
--
--   relBounds : (v : s q) -> Ref q (RelBounds (bufSize v))
--
--   ||| Stack of positions used to keep track of the positions of
--   ||| opening parentheses and brackets.
--   positions : s q -> Ref q (SnocList BytePos)
--
-- ||| Returns the current substring of the byte vector
-- ||| (corresponding to the position and length of the current
-- ||| token).
-- |||
-- ||| The remainder of the previous bytestring is prefixed in case
-- ||| we are currently at position zero.
-- export %inline
-- getBytes : HasBytes s => (sk : s q) => F1 q ByteString
-- getBytes t =
--   let RB from till # t := read1 (relBounds sk) t
--    in case from of
--         0 => (prev sk <+> bytesFromTill (cur sk) from till) # t
--         _ => bytesFromTill (cur sk) from till # t
--
-- export %inline
-- toFinalPos : HasBytes s => (sk : s q) => F1' q
-- toFinalPos = write1 (relBounds sk) (final $ bufSize sk)
--
-- ||| A parser is a system of automata, where each
-- ||| lexicographic token determines the next automaton
-- ||| state plus lexer to use.
-- public export
-- record P1 (q,e : Type) (a : Type) where
--   constructor P
--   {states    : Bits32}
--   {0 state   : Type -> Type}
--   init       : Index states
--   stck       : (size : Nat) -> IBuffer size -> F1 q (state q)
--   lex        : Lex1 q states state
--   chunk      : state q -> F1 q (Maybe a)
--   err        : Arr32 states (state q -> F1 q e)
--   eoi        : Index states -> state q -> F1 q (Either e a)
--   {auto hasb : HasBytes state}
--
-- public export
-- 0 PST : (p : P1 q e a) -> Type
-- PST p = p.state q
--
-- public export
-- 0 PIx : (p : P1 q e a) -> Type
-- PIx p = Index p.states
--
-- public export
-- 0 PStep : (p : P1 q e a) -> Type
-- PStep p = Step q p.states p.state
--
-- public export
-- 0 PRun : (p : P1 q e a) -> Type
-- PRun p = Run1 q p.states p.state
--
-- public export
-- 0 PIgn : (p : P1 q e a) -> Type
-- PIgn p = Ign1 q p.states p.state
--
-- ||| An array of arrays describing a lexer's state machine.
-- public export
-- 0 PByteStep : Nat -> (p : P1 q e a) -> Type
-- PByteStep n p = IArray 256 (Transition n q p.states p.state)
--
-- ||| An array of arrays describing a lexer's state machine.
-- public export
-- 0 PStepper : Nat -> (p : P1 q e a) -> Type
-- PStepper n p = IArray (S n) (PByteStep n p)
--
-- export
-- arrFail :
--      (0 s : Type -> Type)
--   -> Arr32 r (s q -> F1 q e)
--   -> Index r
--   -> s q
--   -> F1 q (Either e x)
-- arrFail s arr ix st t =
--  let eo      := arr `at` ix
--      err # t := eo st t
--   in Left err # t
--
-- export %inline
-- fail : (p : P1 q e a) -> PIx p -> PST p -> F1 q (Either e x)
-- fail p = arrFail p.state p.err
--
-- export %inline
-- failFun1 : (p : P1 q e a) -> PIx p -> Fun1 q p.state (Either e x)
-- failFun1 p st (E sk t) = arrFail p.state p.err st sk t
--
-- public export
-- 0 Parser1 : (e : Type) -> (a : Type) -> Type
-- Parser1 e a = {0 q : _} -> P1 q e a
--
-- export %inline
-- lex1 : {r : _} -> List (Entry r (DFA q r s)) -> Lex1 q r s
-- lex1 es = arr32 r (dfa []) es

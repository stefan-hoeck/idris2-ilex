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

||| An interface for mutable parser stacks `s` that facilitates
||| parsing string tokens containing escape sequences.
public export
interface HasBytes (0 s : Type -> Type) where
  constructor MkHB
  ||| Returns the remainder of the previous bytestring that should
  ||| be used as the beginning of the current token.
  prev      : s q -> Ref q ByteString

  ||| The byte vector currently being processed.
  cur       : s q -> Ref q ByteString

  ||| Absolute start position of the current token from the beginning
  ||| of the whole byte stream processed so far.
  offset    : s q -> Ref q Nat

  ||| Start position of the current token relative to `cur`.
  |||
  ||| If this is negative, the current token will also include
  ||| `prev`. Reference `len` will still hold the full length
  ||| of the token.
  relpos    : s q -> Ref q Integer

  ||| Length of the current token
  len       : s q -> Ref q Nat

  ||| Stack of positions used to keep track of the positions of
  ||| opening parentheses and brackets.
  positions : s q -> Ref q (SnocList BytePos)

||| Returns the current substring of the byte vector
||| (corresponding to the position and length of the current
||| token).
|||
||| The remainder of the previous bytestring is prefixed in case
||| we are currently at position zero.
export %inline
getBytes : HasBytes s => (sk : s q) => F1 q ByteString
getBytes = T1.do
  bs   <- read1 (cur sk)
  p    <- read1 (relpos sk)
  l    <- read1 (len sk)
  case prim__lt_Integer p 0 of
    0 => pure (substring (cast p) l bs)
    n => read1 (prev sk) >>= \pre =>
           pure (pre <+> take (cast $ cast l + p) bs)

||| A parser is a system of automata, where each
||| lexicographic token determines the next automaton
||| state plus lexer to use.
public export
record P1 (q,e : Type) (a : Type) where
  constructor P
  {states    : Bits32}
  {0 state   : Type -> Type}
  init       : Index states
  stck       : F1 q (state q)
  lex        : Lex1 q states state
  chunk      : state q -> F1 q (Maybe a)
  err        : Arr32 states (state q -> F1 q e)
  eoi        : Index states -> state q -> F1 q (Either e a)
  {auto hasb : HasBytes state}

public export
0 PST : (p : P1 q e a) -> Type
PST p = p.state q

public export
0 PIx : (p : P1 q e a) -> Type
PIx p = Index p.states

public export
0 PStep : (p : P1 q e a) -> Type
PStep p = Step q p.states p.state

||| An array of arrays describing a lexer's state machine.
public export
0 PByteStep : Nat -> (p : P1 q e a) -> Type
PByteStep n p = IArray 256 (Transition n q p.states p.state)

||| An array of arrays describing a lexer's state machine.
public export
0 PStepper : Nat -> (p : P1 q e a) -> Type
PStepper n p = IArray (S n) (PByteStep n p)

export
arrFail :
     (0 s : Type -> Type)
  -> Arr32 r (s q -> F1 q e)
  -> Index r
  -> s q
  -> F1 q (Either e x)
arrFail s arr ix st t =
 let eo      := arr `at` ix
     err # t := eo st t
  in Left err # t

export %inline
fail : (p : P1 q e a) -> PIx p -> PST p -> F1 q (Either e x)
fail p = arrFail p.state p.err

public export
0 Parser1 : (e : Type) -> (a : Type) -> Type
Parser1 e a = {0 q : _} -> P1 q e a

export %inline
lex1 : {r : _} -> List (Entry r (DFA q r s)) -> Lex1 q r s
lex1 es = arr32 r (dfa []) es

module Text.ILex.Parser

import Derive.Prelude
import Data.Buffer
import public Data.Prim.Bits32
import public Data.ByteString
import public Data.Linear.Ref1
import public Text.Bounds
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

||| An interface for mutable parser stacks `s` that allows
||| the parse loop to register the byte string corresponding to
||| the currently parsed token.
public export
interface HasBytes (0 s : Type -> Type) where
  constructor MkHB
  bytes : s q -> Ref q ByteString

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

||| A parser is a system of automata, where each
||| lexicographic token determines the next automaton
||| state plus lexer to use.
public export
record P1 (q,e : Type) (r : Bits32) (s : Type -> Type) (a : Type) where
  constructor P
  init  : Index r
  stck  : F1 q (s q)
  lex   : Lex1 q r s
  chunk : s q -> F1 q (Maybe a)
  err   : Arr32 r (s q -> F1 q e)
  eoi   : Index r -> s q -> F1 q (Either e a)
  {auto hasb : HasBytes s}

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
fail : P1 q e r s a -> Index r -> s q -> F1 q (Either e x)
fail = arrFail s . err

export
lastStep : P1 q e r s a -> Step1 q r s -> Index r -> s q -> F1 q (Either e a)
lastStep p f st stck t =
  let r # t := f (stck # t)
      _ # t := write1 (bytes @{p.hasb} stck) "" t
   in p.eoi r stck t

public export
0 Parser1 : (e : Type) -> (r : Bits32) -> (s : Type -> Type) -> (a : Type) -> Type
Parser1 e r s a = {0 q : _} -> P1 q e r s a

export %inline
lex1 : {r : _} -> List (Entry r (DFA q r s)) -> Lex1 q r s
lex1 es = arr32 r (dfa []) es

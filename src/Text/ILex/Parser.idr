module Text.ILex.Parser

import Derive.Prelude
import Data.Buffer
import public Data.Prim.Bits32
import public Data.ByteString
import public Data.Linear.Ref1
import public Text.ILex.Bounds
import public Text.ILex.Error
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

public export
record Index (n : Bits32) where
  constructor I
  val : Bits32
  {auto 0 prf : val < n}

%runElab deriveIndexed "Index" [Show,Eq,Ord]

public export
fromInteger : (n : Integer) -> (0 p : cast n < r) => Index r
fromInteger n = I (cast n)

public export
Ini : (0 prf : 0 < n) => Index n
Ini = I 0

public export
Done : {n : _} -> (0 prf : (n-1) < n) => Index n
Done = I (n-1)

||| An interface for mutable parser stacks `s` that allows
||| the parse loop to register the byte string corresponding to
||| the currently parsed token.
public export
interface HasBytes (0 s : Type -> Type) where
  bytes : s q -> Ref q ByteString

public export
data Step : (q,e : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type where
  Go  : ((1 sk : R1 q (s q)) -> R1 q (Index r)) -> Step q e r s
  Rd  : ((1 sk : R1 q (s q)) -> R1 q (Index r)) -> Step q e r s
  Err : Step q e r s

public export
0 Steps : (q,e : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
Steps q e r s = TokenMap (Step q e r s)

public export
0 BStep : (q,e : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
BStep q e = Step q (BoundedErr e)

public export
0 BSteps : (q,e : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
BSteps q e r s = TokenMap (BStep q e r s)

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
0 DFA1 : (q,e : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
DFA1 q e r s = DFA (Step q e r s)

public export
0 Lex1 : (q,e : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
Lex1 q e r s = Arr32 r (DFA1 q e r s)

||| A parser is a system of automata, where each
||| lexicographic token determines the next automaton
||| state plus lexer to use.
public export
record P1 (q,e : Type) (r : Bits32) (s : Type -> Type) (a : Type) where
  constructor P
  init  : Index r
  stck  : F1 q (s q)
  lex   : Lex1 q e r s
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
lastStep :
     P1 q e r s a
  -> Step q e r s
  -> Index r
  -> s q
  -> F1 q (Either e a)
lastStep p v st stck t =
  case v of
    Go f =>
     let r # t := f (stck # t)
         _ # t := write1 (bytes @{p.hasb} stck) "" t
      in p.eoi r stck t
    Rd f =>
     let r # t := f (stck # t)
         _ # t := write1 (bytes @{p.hasb} stck) "" t
      in p.eoi r stck t
    Err    => fail p st stck t

public export
0 Parser1 : (e : Type) -> (r : Bits32) -> (s : Type -> Type) -> (a : Type) -> Type
Parser1 e r s a = {0 q : _} -> P1 q e r s a

export %inline
lex1 : {r : _} -> List (Entry r (DFA1 q e r s)) -> Lex1 q e r s
lex1 es = arr32 r (dfa Err []) es

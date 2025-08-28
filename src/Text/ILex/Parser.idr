module Text.ILex.Parser

import public Data.ByteString
import public Data.Linear.Token
import public Text.ILex.RExp
import public Text.ILex.Lexer

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "scheme:(lambda (x) (make-vector x))"
         "javascript:lambda:(n,w) => new Array(n)"
prim__emptyMachine : Bits32 -> PrimIO AnyPtr

%foreign "scheme:(lambda (x i) (vector-ref x i))"
         "javascript:lambda:(x,bi) => x[bi]"
prim__machineGet : AnyPtr -> Bits32 -> AnyPtr

%foreign "scheme:(lambda (x i w) (vector-set! x i w))"
         "javascript:lambda:(x,i,w) => {x[i] = w}"
prim__machineSet : AnyPtr -> Bits32 -> (val : AnyPtr) -> PrimIO ()

public export
record BSI (q : Type) (s : Type -> Type) where
  constructor B
  stack1 : s q
  bytes1 : ByteString
  1 tok1 : T1 q

public export
0 S1 : (q : Type) -> (s : Type -> Type) -> (a : Type) -> Type
S1 q s a = (1 sk : R1 q (s q)) -> R1 q a

public export
0 SBS1 : (q : Type) -> (s : Type -> Type) -> (a : Type) -> Type
SBS1 q s a = (1 sk : BSI q s) -> R1 q a

public export
data Step1 : (q,e,r : Type) -> (s : Type -> Type) -> Type where
  Go  : S1 q s r -> Step1 q e r s
  Rd  : SBS1 q s r -> Step1 q e r s
  Prs : SBS1 q s (Either e r) -> Step1 q e r s
  Err : Step1 q e r s

export
record Lex1 (q,e,r : Type) (s : Type -> Type) where
  constructor L1
  ptr : AnyPtr

||| A parser is a system of automata, where each
||| lexicographic token determines the next automaton
||| state plus lexer to use.
public export
record P1 (q,e,r : Type) (s : Type -> Type) (a : Type) where
  constructor P
  init  : r
  stck  : F1 q (s q)
  lex   : Lex1 q e r s
  chunk : s q -> F1 q (Maybe a)
  err   : r -> s q -> ByteString -> F1 q e
  eoi   : r -> s q -> F1 q (Either e a)

export
fail : P1 q e r s a -> r -> s q -> ByteString -> F1 q (Either e x)
fail p r s bs t = let x # t := p.err r s bs t in Left x # t

export
lastStep :
     P1 q e r s a
  -> Step1 q e r s
  -> r
  -> s q
  -> ByteString
  -> F1 q (Either e a)
lastStep p (Go f)  st stck bs t =
 let r # t := f (stck # t) in p.eoi r stck t
lastStep p (Rd f)  st stck bs t =
 let r # t := f (B stck bs t) in p.eoi r stck t
lastStep p (Prs f) st stck bs t =
 let Right r # t := f (B stck bs t) | Left x # t => Left x # t
  in p.eoi r stck t
lastStep p Err st stck bs t = fail p st stck bs t

public export
0 Parser1 : (e,r : Type) -> (s : Type -> Type) -> (a : Type) -> Type
Parser1 e r s a = {0 q : _} -> P1 q e r s a

export
dfa1 : Lex1 q e r s -> r -> DFA (Step1 q e r s)
dfa1 (L1 p) x = believe_me $ prim__machineGet p (believe_me x)

public export
0 DFA1 : (q,e,r : Type) -> (s : Type -> Type) -> Type
DFA1 q e r s = DFA (Step1 q e r s)

public export
record SInfo (q,e,r : Type) (s : Type -> Type) where
  constructor SI
  state : r
  sdfa  : DFA1 q e r s

export
lex1 : List (SInfo q e r s) -> Lex1 q e r s
lex1 is =
  run1 $ \t =>
   let ptr # t := ffi (prim__emptyMachine (cast $ length is)) t
    in fill is ptr t

  where
    fill : List (SInfo q e r s) -> AnyPtr -> F1 x (Lex1 q e r s)
    fill []              ptr t = L1 ptr # t
    fill (SI x d :: xs) ptr t =
     let _ # t := ffi (prim__machineSet ptr (believe_me x) (believe_me d)) t
      in fill xs ptr t

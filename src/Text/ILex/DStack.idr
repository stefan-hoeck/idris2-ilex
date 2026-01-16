||| This module provides an experimental alternative
||| to `Text.ILex.Stack` with a correctly typed parser
||| stack.
module Text.ILex.DStack

import Syntax.T1
import Text.ILex.Interfaces
import Text.ILex.Parser

%default total

--------------------------------------------------------------------------------
-- Dependent Parser Stack
--------------------------------------------------------------------------------

export
infixr 7 :>

public export
data Stack : (s : List Type -> Type) -> List Type -> Type where
  Nil  : Stack s []
  (:>) : (st : s ts) -> Stack s ts -> Stack s []
  (::) : (v : t)     -> Stack s ts -> Stack s (t::ts)

public export %inline
push : {0 s : _} -> s [t] -> (v : t) -> Stack s [] -> Stack s []
push st v stck = st :> v :: stck

--------------------------------------------------------------------------------
-- Mutable, Dependent Parser State
--------------------------------------------------------------------------------

public export
record DStack (s : List Type -> Type) (e : Type) (q : Type) where
  [search q]
  constructor S
  line_      : Ref q Nat
  col_       : Ref q Nat
  positions_ : Ref q (SnocList Position)
  strings_   : Ref q (SnocList String)
  stack_     : Ref q (Stack s [])
  error_     : Ref q (Maybe $ BoundedErr e)
  bytes_     : Ref q ByteString

||| Initializes a new parser stack.
export
init : {default Nil st : Stack s []} -> F1 q (DStack s e q)
init = T1.do
  ln <- ref1 Z
  cl <- ref1 Z
  ps <- ref1 [<]
  ss <- ref1 [<]
  sk <- ref1 st
  er <- ref1 Nothing
  bs <- ref1 empty
  pure (S ln cl ps ss sk er bs)

export %inline
HasStack (DStack s e) (Stack s []) where
  stack = stack_

export %inline
HasError (DStack s e) e where
  error = error_

export %inline
HasPosition (DStack s e) where
  line = line_
  col  = col_
  positions = positions_

export %inline
HasBytes (DStack s e) where
  bytes = bytes_

export %inline
HasStringLits (DStack s e) where
  strings = strings_

public export
0 StateTrans : (s : List Type -> Type) -> Type
StateTrans s = Stack s [] -> Stack s []

public export
0 StateAct : Type -> (s : List Type -> Type) -> Type -> Type
StateAct q s a = Stack s [] -> F1 q a

export %inline
dmod : (sk : DStack s e q) => a -> StateTrans s -> F1 q a
dmod res f t =
 let st # t := read1 sk.stack_ t
  in writeAs sk.stack_ (f st) res t

export %inline
dmodAs : Cast (Stack s []) a => (sk : DStack s e q) => StateTrans s -> F1 q a
dmodAs f t =
 let st # t := read1 sk.stack_ t
     st2    := f st
  in writeAs sk.stack_ st2 (cast st2) t

export %inline
dput : (sk : DStack s e q) =>  Stack s [] -> a -> F1 q a
dput st v = writeAs sk.stack_ st v

export %inline
dact : (sk : DStack s e q) => (act : StateAct q s a) -> F1 q a
dact f t =
 let st # t := read1 sk.stack_ t
  in f st t

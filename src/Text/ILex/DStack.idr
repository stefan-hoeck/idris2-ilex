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
data Stack : Bool -> (s : List Type -> Type) -> List Type -> Type where
  Nil  : Stack False s []
  (:>) : (st : s ts) -> Stack b s ts -> Stack True s []
  (::) : (v : t)     -> Stack b s ts -> Stack False s (t::ts)

public export %inline
push : {0 s : _} -> s [t] -> (v : t) -> Stack b s [] -> Stack True s []
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
  stack_     : Ref q (Stack True s [])
  error_     : Ref q (Maybe $ BoundedErr e)
  bytes_     : Ref q ByteString

||| Initializes a new parser stack.
export
init : Stack True s [] -> F1 q (DStack s e q)
init st = T1.do
  ln <- ref1 Z
  cl <- ref1 Z
  ps <- ref1 [<]
  ss <- ref1 [<]
  sk <- ref1 st
  er <- ref1 Nothing
  bs <- ref1 empty
  pure (S ln cl ps ss sk er bs)

export %inline
HasStack (DStack s e) (Stack True s []) where
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
0 StateAct : Type -> (s : List Type -> Type) -> Bits32 -> Type
StateAct q s r =
     {0 b : _}
  -> {0 ts : _}
  -> s ts
  -> Stack b s ts
  -> F1 q (Index r)

parameters {auto sk : DStack s e q}

  export %inline
  dact : StateAct q s r -> F1 q (Index r)
  dact f t =
   let (st:>x) # t := read1 sk.stack_ t
    in f st x t

  export %inline
  dput : s ts -> Cast (s ts) a => Stack b s ts -> F1 q a
  dput st x = writeAs sk.stack_ (st:>x) (cast st)

  export %inline
  dpush : s [t] -> Cast (s [t]) a => t -> F1 q a
  dpush st v t =
   let stck # t := read1 sk.stack_ t
    in writeAs sk.stack_ (st:>v::stck) (cast st) t

  export %inline
  derr : s [] -> Cast (s []) a => s ts -> Stack b s ts -> F1 q a
  derr err st x = writeAs sk.stack_ (err:>st:>x) (cast err)

module Text.ILex.State.Streaming

import Data.Linear.Ref1
import Syntax.T1
import Text.ByteBounds
import Text.ILex.Interfaces
import Text.ILex.Parser
import Text.ILex.State.Derive
import Text.ILex.Util
import Text.ParseError

%default total
%language ElabReflection

||| A parser state that can be use for streaming lists of values
||| such as declarations in a programming language.
|||
||| The parser stack is stored in mutable field `stack_`, while
||| the values parsed so far are stored in `values_`.
public export
record State (e,s,a : Type) (r : Bits32) (q : Type) where
  [search q]
  constructor SS
  -- Position and token bounds
  bufSize_    : Nat
  prev_       : ByteString
  cur_        : IBuffer bufSize_
  prevOffset_ : Nat
  curOffset_  : Nat
  from_       : Ref q (LTENat bufSize_)
  till_       : Ref q (LTENat bufSize_)
  positions_  : Ref q (SnocList BytePos)

  -- Current state
  stack_     : Ref q s
  state_     : Ref q (Index r)
  values_    : Ref q (SnocList a)

  -- Working with string literals
  strings_   : Ref q (SnocList String)

  -- Error handling
  error_     : Ref q (Maybe $ BBErr e)

  -- Block comments
  comment    : Index r
  depth      : Ref q Nat

%runElab derive "State" [FullState]

export
init :
     (comment : Index r)
  -> (stack   : s)
  -> (n : Nat)
  -> IBuffer n
  -> F1 q (State e s a r q)
init c v n buf = T1.do
  rf <- ref1 (first n)
  rt <- ref1 (first n)
  ps <- ref1 [<]
  sk <- ref1 v
  st <- ref1 c
  ds <- ref1 [<]
  ss <- ref1 [<]
  er <- ref1 Nothing
  dp <- ref1 Z
  pure (SS n empty buf 0 0 rf rt ps sk st ds ss er c dp)

export %inline
pushValue : State e s a r q => a -> s -> Index r -> F1 q (Index r)
pushValue @{st} d sk x t =
 let _ # t := push1 st.values_ d t
  in writeAs st.stack_ sk x t

export
values : State e s a r q -> F1 q (Either x $ List a)
values st t =
 let sd # t := replace1 st.values_ [<] t
  in Right (sd <>> []) # t

export
valuesChunk : State e s a r q -> F1 q (Maybe $ List a)
valuesChunk st t =
 let sd # t := replace1 st.values_ [<] t
  in maybeList sd # t

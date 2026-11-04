module Text.ILex.Dependent.Stack

import public Text.ByteBounds
import public Text.ILex.Dependent.Parser

%default total

--------------------------------------------------------------------------------
-- List Stack
--------------------------------------------------------------------------------

public export
0 Val : Bool -> (r,a : Type) -> Type
Val False r a = r
Val True  r a = a

public export
data Stack : Bool -> (r, a : Type) -> Type where
  Lin  : Stack False r a
  (:<) : Stack b r a -> Val b r a -> Stack True r a

export
root : Stack True r a -> r
root [<v]           = v
root (s@(sv:<_):<_) = root s

acc : List a -> Stack b r a -> Val b r a -> (r, List a)
acc as [<]     c = (c, as)
acc as (sv:<v) c = acc (c::as) sv v

export %inline
collapse : Stack True r a -> (r,List a)
collapse (sv:<v) = acc [] sv v

export
collapseString : Stack True r String -> (r,String)
collapseString s =
  case collapse s of
    (r,[])  => (r,"")
    (r,[x]) => (r,x)
    (r,xs)  => (r,fastConcat xs)

export %inline
app :
     {0 l      : Type -> Type}
  -> (x        : RExp True)
  -> (lex      : l (Stack True r a))
  -> (va       : a)
  -> (RExp True, DStep l (Stack True r a))
app x lex va = (x, Run $ \i => E lex (i.val :< va))

export %inline
appString :
     {0 l      : Type -> Type}
  -> (x        : RExp True)
  -> (lex      : l (Stack True r a))
  -> (va       : String -> a)
  -> (RExp True, DStep l (Stack True r a))
appString x lex va = (x, Run $ \i => E lex (i.val :< va (getString i)))

export %inline
appBytes :
     {0 l      : Type -> Type}
  -> (x        : RExp True)
  -> (lex      : l (Stack True r a))
  -> (va       : ByteString -> a)
  -> (RExp True, DStep l (Stack True r a))
appBytes x lex va = (x, Run $ \i => E lex (i.val :< va (getBytes i)))

--------------------------------------------------------------------------------
-- Stack Root plus Bounds
--------------------------------------------------------------------------------

public export
record Root (p : Type -> Type) where
  constructor R
  {auto prf : p ptpe}
  parent    : ptpe
  bounds    : ByteBounds

export %inline
opn :
     {0 p,l    : Type -> Type}
  -> {auto prf : p t}
  -> (x        : RExp True)
  -> (lex      : l (Stack True (Root p) a))
  -> (RExp True, DStep l t)
opn x lex = (x, Run $ \i => E lex [< R i.val $ bounds i])

export %inline
close :
     {0 p      : Type -> Type}
  -> (x        : RExp True)
  -> (cls      : {0 t : _} -> p t => List a -> t -> r)
  -> (RExp True, Stp (Stack True (Root p) a) r)
close x cls = (x, Run $ \i => let (R v _, vs) := collapse i.val in cls vs v)

export %inline
closeStr :
     {0 p      : Type -> Type}
  -> (x        : RExp True)
  -> (cls      : {0 t : _} -> p t => String -> t -> r)
  -> (RExp True, Stp (Stack True (Root p) String) r)
closeStr x cls =
  (x, Run $ \i => let (R v _, vs) := collapseString i.val in cls vs v)

module Text.ILex.Dependent.Parser

import Data.Buffer
import public Data.ByteString
import public Data.TArray
import public Text.ByteBounds
import public Text.ILex.DFA
import public Text.ILex.Dependent.Bytes
import public Text.ParseError

%default total

public export
0 Stp : (s,a : Type) -> Type
Stp s a = Trans (In s -> a)

public export
0 Stps : (s,a : Type) -> Type
Stps s a = TokenMap (Stp s a)

parameters {0 s,a : Type}
           (vx    : RExp True)

  export %inline
  ignore : (RExp True,Stp s a)
  ignore = (vx, Ign)

  export %inline
  step : (In s -> a) -> (RExp True, Stp s a)
  step f = (vx, Run f)

  export %inline
  vstep : (s -> a) -> (RExp True, Stp s a)
  vstep f = (vx, Run $ f . val)

  export %inline
  bytes : (ByteString -> s -> a) -> (RExp True, Stp s a)
  bytes f = (vx, Run $ \i => f (getBytes i) i.val)

  export %inline
  string : (String -> s -> a) -> (RExp True, Stp s a)
  string f = (vx, Run $ \i => f (getString i) i.val)

export
jsonSpace : RExp True
jsonSpace = oneof [' ','\t','\n','\r']

export %inline
jsonSpaces : RExp True
jsonSpaces = plus jsonSpace

export %inline
jsonSpaced : Stps s a -> Stps s a
jsonSpaced xs = ignore jsonSpaces :: xs

public export
0 Result : (p : Type -> Type) -> Type
Result p = Entry p Prelude.id

export %inline
stepTo : {0 p : _} -> x -> p t -> (In s -> t) -> (x, Stp s $ Result p)
stepTo vx v f = (vx, Run (E v . f))

export %inline
to : {0 p : _} -> x -> p t -> (x, Stp t $ Result p)
to vx v = (vx, Run (E v . val))

public export
0 DStep : (p : Type -> Type) -> Type -> Type
DStep p t = Stp t (Result p)

public export
0 DSteps : (p : Type -> Type) -> Type -> Type
DSteps p t = Stps t (Result p)

public export
0 DFun : Type -> Type -> Type
DFun a t = In t -> a

public export
0 Run : (p : Type -> Type) -> Type -> Type
Run p x = In x -> Result p

||| An array of arrays describing a lexer's state machine.
public export
0 DDFA : (p : Type -> Type) -> Type -> Type
DDFA p x = DFA (Run p x)

||| A parser is a system of automata, where each
||| lexicographic token determines the next automaton
||| state plus lexer to use.
public export
record IParser (e,a : Type) where
  constructor P
  {0 lexer   : Type -> Type}
  {0 itpe    : Type}
  init       : lexer itpe
  istack     : itpe
  lex        : TArray lexer (DDFA lexer)
  err        : TArray lexer (DFun e)
  eoi        : TArray lexer (DFun $ Either e a)
  {lexers    : Bits32}
  {auto en   : TEnum lexer lexers}

public export
0 PStep : (p : IParser e a) -> Type -> Type
PStep p i = Stp i (Result p.lexer)

public export
0 PRun : (p : IParser e a) -> Type -> Type
PRun p t = Run p.lexer t

||| An array of arrays describing a lexer's stack machine.
public export
0 PByteTrans : Nat -> (p : IParser e a) -> Type -> Type
PByteTrans n p t = IArray 256 (Transition n $ PRun p t)

||| An array of arrays describing a lexer's stack machine.
public export
0 PMachine : Nat -> (p : IParser e a) -> Type -> Type
PMachine n p t = IArray (S n) (PByteTrans n p t)

parameters {0 p     : Type -> Type}
           {n       : Bits32}
           {auto en : TEnum p n}

  export %inline
  arrErr : Entries p (DFun $ BBErr e) -> TArray p (DFun $ BBErr e)
  arrErr = tarray _ _ $ unexpectedErr []

  export %inline
  arrEOI :
       Entries p (DFun $ Either (BBErr e) a)
    -> TArray p (DFun $ Either (BBErr e) a)
  arrEOI = tarray _ _ $ failUnexpected []

  export %inline
  lexers : Entries p (DDFA p) -> TArray p (DDFA p)
  lexers = tarray _ _ $ dfa []

parameters (p  : IParser e a)

  export %inline
  failI : p.lexer t -> In t -> Either e x
  failI i arg = Left $ TArray.at @{p.en} p.err i arg

  export %inline
  eoi : p.lexer t -> In t -> Either e a
  eoi i arg = TArray.at @{p.en} p.eoi i arg

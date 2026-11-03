module Text.ILex.Lexer

import public Text.ILex.DFA
import public Data.Enum
import Data.ByteString
import Data.Linear.Token

%default total

public export
record Env (q : Type) (s : Type -> Type) where
  constructor E
  state   : s q
  1 token : T1 q

public export
0 Step1 : (q : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
Step1 q r s = s q -> F1 q (Index r)

public export
0 Fun1 : (q : Type) -> (s : Type -> Type) -> Type -> Type
Fun1 q s a = (1 sk : Env q s) -> R1 q a

public export
0 Run1 : (q : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
Run1 q r s = Fun1 q s (Index r)

public export
0 Step : (q : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
Step q r s = Res (Run1 q r s)

export %inline
toState : Index r -> Step q r s
toState v = Run $ \(E _ t) => v # t

||| An array of arrays describing a lexer's state machine.
public export
0 ByteStep : Nat -> (q : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
ByteStep n q r s = IArray 256 (Transition n $ Run1 q r s)

||| An array of arrays describing a lexer's state machine.
public export
0 Stepper : Nat -> (q : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
Stepper n q r s = IArray (S n) (ByteStep n q r s)

||| A discrete finite automaton (DFA) encoded as
||| an array of state transitions plus an array
||| describing the terminal token states.
public export
0 DFA1 : (q : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
DFA1 q r s = DFA (Run1 q r s)

public export
0 Steps : (q : Type) -> (r : Bits32) -> (s : Type -> Type) -> Type
Steps q r s = TokenMap (Step q r s)

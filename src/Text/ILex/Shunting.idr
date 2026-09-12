module Text.ILex.Shunting

import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Operator Precedence
--------------------------------------------------------------------------------

||| Infix operator associativity
public export
data Assoc = None | InfixR | InfixL

%runElab derive "Assoc" [Show,Eq,Ord]

||| Infix operator associativity and precedence
public export
data Precedence : Type where
  Prefix : (prec : Nat) -> Precedence
  Infix  : (prec : Nat) -> (assoc : Assoc) -> Precedence

%runElab derive "Precedence" [Show,Eq]

export %inline
toPrec : Cast o Precedence => o -> Precedence
toPrec = cast

export
prec : Cast o Precedence => o -> Nat
prec v =
  case toPrec v of
    Prefix p  => p
    Infix p _ => p

public export
data ShuntingErr : Type -> Type where
  AssocNone      : (op : o) -> (prec : Precedence) -> ShuntingErr o
  ExpectedInfix  : (op : o) -> (prec : Precedence) -> ShuntingErr o
  ExpectedPrefix : (op : o) -> (prec : Precedence) -> ShuntingErr o

%runElab derive "ShuntingErr" [Show,Eq]

public export
0 Tok : (t,o : Type) -> Type
Tok t o = Either o (t,o)

public export
0 Toks : (t,o : Type) -> Type
Toks t o = List (Tok t o)

public export
0 Skot : (t,o : Type) -> Type
Skot t o = SnocList (Tok t o)

--------------------------------------------------------------------------------
-- Shunting Yard Implementation
--------------------------------------------------------------------------------

0 Stack : Type -> Type
Stack o = SnocList (o, Precedence)

0 Itm : (o, Precedence) -> Type -> Type
Itm (_,Prefix _) t = ()
Itm _            t = t

%inline
Cast (o,Precedence) Precedence where cast = snd

data Queue : (so : Stack o) -> Type -> Type where
  Lin  : Queue [<] t
  (:<) : {0 p : _} -> Queue s t -> Itm p t -> Queue (s:<p) t

record Insert (t,o : Type) where
  constructor I
  ops   : Stack o
  terms : Queue ops t

parameters {0 t,o    : Type}
           {auto cst : Cast o Precedence}
           (inf      : t -> o -> t -> t)
           (pre      : o -> t -> t)

  0 Res : Type
  Res = Either (ShuntingErr o) (Insert t o)

  app : (p : (o,Precedence)) -> Itm p t -> t -> t
  app (op, Prefix {}) _ y = pre op y
  app (op, Infix {})  x y = inf x op y

  apply : (s : Stack o) -> Queue s t -> t -> t
  apply [<]     [<]     lst = lst
  apply (sp:<p) (si:<i) lst = apply sp si (app p i lst)

  insInf : (s : Stack o) -> Queue s t -> t -> o -> Nat -> Assoc -> Res
  insInf [<]     [<]     lst op n a = Right $ I [<(op,Infix n a)] [<lst]
  insInf (sp:<p) (si:<i) lst op n a =
    case compare (prec p) n of
      LT => Right $ I (sp:<p:<(op,Infix n a)) (si:<i:<lst)
      GT => insInf sp si (app p i lst) op n a
      EQ => ?eqcase
--        let False := isLeftAssoc op | True => insert st so (app t o lst) op
--            False := notAssoc op    | True => Left (AssocNone op $ cast op)
--            False := notAssoc o     | True => Left (AssocNone o $ cast o)
--         in Right $ I (st:<t:<lst) (so:<o:<op)

  impl : (s : Stack o) -> Queue s t -> Toks t o -> t -> Either (ShuntingErr o) t
  impl s q []      lst = Right $ apply s q lst
  impl s q (i::is) lst =
    case i of
      Left op      => case cast {to = Precedence} op of
        Prefix n => impl (s:<(op,Prefix n)) (q:<()) is lst
        p        => Left (ExpectedPrefix op p)
      Right (t,op) => case cast {to = Precedence} op of
        Infix n a => case insInf s q t op n a of
          Left err        => Left err
          Right (I s2 q2) => impl s2 q2 is lst
        p         => Left (ExpectedInfix op p)

  ||| An implementation of the
  ||| [shunting yard algorithm](https://en.wikipedia.org/wiki/Shunting_yard_algorithm)
  ||| used to convert term-operator chains such as `1 + 2 * 3 ^ 4` to proper
  ||| syntax trees based on the operators' associativity and precedence.
  export %inline
  shuntingYard : Skot t o -> t -> Either (ShuntingErr o) t
  shuntingYard = impl [<] [<] . (<>> [])

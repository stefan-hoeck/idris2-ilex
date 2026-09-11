module Text.ILex.Shunting

import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Operator Precedence
--------------------------------------------------------------------------------

||| Operator associativity
public export
data Assoc = None | InfixR | InfixL

%runElab derive "Assoc" [Show,Eq,Ord]

||| Infix operator associativity and precedence
public export
record Precedence where
  constructor P
  value : Nat
  assoc : Assoc

%runElab derive "Precedence" [Show,Eq,Ord]

export %inline
compareOp : Cast o Precedence => o -> o -> Ordering
compareOp = compare `on` cast {to = Precedence}

export %inline
notAssoc : Cast o Precedence => o -> Bool
notAssoc op = assoc (cast op) == None

export %inline
isLeftAssoc : Cast o Precedence => o -> Bool
isLeftAssoc op = assoc (cast op) == InfixL

--------------------------------------------------------------------------------
-- Basic Shunting Yard
--------------------------------------------------------------------------------

data Stack : Nat -> Type -> Type where
  Lin  : Stack 0 a
  (:<) : Stack n a -> a -> Stack (S n) a

record Insert (o,t : Type) where
  constructor I
  {0 size : Nat}
  terms : Stack size t
  ops   : Stack size o

public export
data ShuntingErr : Type -> Type where
  AssocNone : (op : o) -> (prec : Precedence) -> ShuntingErr o

%runElab derive "ShuntingErr" [Show,Eq]

parameters {0 t,o    : Type}
           {auto cst : Cast o Precedence}
           (app      : t -> o -> t -> t)

  apply : Stack n t -> Stack n o -> t -> t
  apply [<]     [<]     lst = lst
  apply (st:<t) (so:<o) lst = apply st so (app t o lst)

  insert : Stack n t -> Stack n o -> t -> o -> Either (ShuntingErr o) (Insert o t)
  insert [<]     [<]     lst op = Right $ I [<lst] [<op]
  insert (st:<t) (so:<o) lst op =
    case compare (value $ cast @{cst} o) (value $ cast op) of
      LT => Right $ I (st:<t:<lst) (so:<o:<op)
      GT => insert st so (app t o lst) op
      EQ =>
       let False := isLeftAssoc op | True => insert st so (app t o lst) op
           False := notAssoc op    | True => Left (AssocNone op $ cast op)
           False := notAssoc o     | True => Left (AssocNone o $ cast o)
        in Right $ I (st:<t:<lst) (so:<o:<op)

  impl : Stack n t -> Stack n o -> List (t,o) -> t -> Either (ShuntingErr o) t
  impl st so []           lst = Right $ apply st so lst
  impl st so ((x,op)::ps) lst =
   let Right (I st2 so2) := insert st so x op | Left x => Left x
    in impl st2 so2 ps lst

  ||| A basic implementation of the
  ||| [shunting yard algorithm](https://en.wikipedia.org/wiki/Shunting_yard_algorithm)
  ||| used to convert term-operator chains such as `1 + 2 * 3 ^ 4` to proper
  ||| syntax trees based on the operators' associativity and precedence.
  export %inline
  shuntingYard : SnocList (t,o) -> t -> Either (ShuntingErr o) t
  shuntingYard = impl [<] [<] . (<>> [])

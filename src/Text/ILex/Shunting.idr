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

export
nonAssoc : Cast o Precedence => o -> Bool
nonAssoc v =
  case toPrec v of
    Infix _ None => True
    _            => False

export
isInfixL : Cast o Precedence => o -> Bool
isInfixL v =
  case toPrec v of
    Infix _ InfixL => True
    _              => False

public export
data ShuntingErr : Type -> Type where
  AssocNone      : (op : o) -> (prec : Precedence) -> ShuntingErr o
  ExpectedInfix  : (op : o) -> (prec : Precedence) -> ShuntingErr o
  ExpectedPrefix : (op : o) -> (prec : Precedence) -> ShuntingErr o

%runElab derive "ShuntingErr" [Show,Eq]

||| Shunting yard algorithm input token.
||| A token is either a term followed by an infix operator
||| or a single prefix operator
public export
data Tok : (t,o : Type) -> Type where
  TPre : o -> (prec : Nat) -> Tok t o
  TInf : t -> o -> (prec : Nat) -> Assoc -> Tok t o

export
Cast (Tok t o) Precedence where
  cast (TPre _ p)     = Prefix p
  cast (TInf _ _ p a) = Infix p a

export
Cast (Tok t o) o where
  cast (TPre o _)     = o
  cast (TInf _ o _ _) = o

public export
0 Toks : (t,o : Type) -> Type
Toks t o = List (Tok t o)

public export
0 Skot : (t,o : Type) -> Type
Skot t o = SnocList (Tok t o)

public export
data IsInfix : Precedence -> Type where
  ItIsInfix : IsInfix (Infix p a)

public export
data IsPrefix : Precedence -> Type where
  ItIsPrefix : IsPrefix (Prefix p)

%inline
tinf_ : t -> o -> (p : Precedence) -> (0 prf : IsInfix p) => Tok t o
tinf_ x y (Infix p a) = TInf x y p a

||| Smart constructor for `TInf`.
export %inline
tinf : Cast o Precedence => t -> (v : o) -> (0 prf : IsInfix (cast v)) => Tok t o
tinf x v = tinf_ x v (cast v)

%inline
tpre_ : o -> (p : Precedence) -> (0 prf : IsPrefix p) => Tok t o
tpre_ y (Prefix p) = TPre y p

||| Smart constructor for `TPre`.
export %inline
tpre : Cast o Precedence => (v : o) -> (0 prf : IsPrefix (cast v)) => Tok t o
tpre x = tpre_ x (cast x)

--------------------------------------------------------------------------------
-- Shunting Yard Implementation
--------------------------------------------------------------------------------

parameters {0 t,o    : Type}
           {auto cst : Cast o Precedence}
           (inf      : t -> o -> t -> t)
           (pre      : o -> t -> t)

  0 Res : Type
  Res = Either (ShuntingErr o) (Skot t o)

  app : Tok t o -> t -> t
  app (TPre op _)     y = pre op y
  app (TInf x op _ _) y = inf x op y

  apply : Skot t o -> t -> t
  apply [<]     lst = lst
  apply (si:<i) lst = apply si (app i lst)

  insInf : Skot t o -> t -> o -> Nat -> Assoc -> Res
  insInf [<]     lst op n a = Right $ [<TInf lst op n a]
  insInf (si:<i) lst op n a =
    case compare (prec i) n of
      LT => Right $ si:<i:<TInf lst op n a
      GT => insInf si (app i lst) op n a
      EQ =>
       let False := isInfixL op | True => insInf si (app i lst) op n a
           False := nonAssoc op | True => Left (AssocNone op $ cast op)
           False := nonAssoc i  | True => Left (AssocNone (cast i) (cast i))
        in Right $ si:<i:<TInf lst op n a

  impl : Skot t o -> Toks t o -> t -> Either (ShuntingErr o) t
  impl si []      lst = Right $ apply si lst
  impl si (i::is) lst =
    case i of
      TPre op n     => impl (si:<TPre op n) is lst
      TInf t op n a => case insInf si t op n a of
        Left err  => Left err
        Right si2 => impl si2 is lst

  ||| An implementation of the
  ||| [shunting yard algorithm](https://en.wikipedia.org/wiki/Shunting_yard_algorithm)
  ||| used to convert term-operator chains such as `1 + 2 * 3 ^ 4` to proper
  ||| syntax trees based on the operators' associativity and precedence.
  export %inline
  shuntingYard : Skot t o -> t -> Either (ShuntingErr o) t
  shuntingYard = impl [<] . (<>> [])

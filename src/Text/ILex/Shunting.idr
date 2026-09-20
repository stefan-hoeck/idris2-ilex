module Text.ILex.Shunting

import Text.ByteBounds
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

export
Interpolation Assoc where
  interpolate None   = "infix"
  interpolate InfixR = "infixr"
  interpolate InfixL = "infixl"

||| Infix operator associativity and precedence
public export
data Precedence : Type where
  Prefix  : (prec : Nat) -> Precedence
  Postfix : (prec : Nat) -> Precedence
  Infix   : (prec : Nat) -> (assoc : Assoc) -> Precedence

%runElab derive "Precedence" [Show,Eq]

export
Interpolation Precedence where
  interpolate (Prefix p)  = "prefix \{show p}"
  interpolate (Postfix p) = "postfix \{show p}"
  interpolate (Infix p a) = "\{a} \{show p}"

export %inline
Cast a Precedence => Cast (ByteBounded a) Precedence where
  cast = cast . val

export %inline
toPrec : Cast o Precedence => o -> Precedence
toPrec = cast

export
prec : Cast o Precedence => o -> Nat
prec v =
  case toPrec v of
    Prefix p  => p
    Postfix p => p
    Infix p _ => p

public export
data ShuntingErr : Type -> Type where
  AssocNone      : (op : o) -> (prec : Precedence) -> ShuntingErr o

%runElab derive "ShuntingErr" [Show,Eq]

export
Interpolation o => Interpolation (ShuntingErr o) where
  interpolate (AssocNone op p) = "operator '\{op}' (\{p}) is non-associative"

||| Shunting yard algorithm input token.
||| A token is either a term followed by an infix operator
||| or a single prefix operator
public export
data Tok : (t,p,i,o : Type) -> Type where
  TPre : ByteBounded p -> (prec : Nat) -> Tok t p i o
  TInf : t -> ByteBounded i -> (prec : Nat) -> Assoc -> Tok t p i o
  TPst : ByteBounded o -> (prec : Nat) -> Tok t p i o

%runElab derive "Tok" [Show,Eq]

export
Cast (Tok t p i o) Precedence where
  cast (TPre _ p)     = Prefix p
  cast (TInf _ _ p a) = Infix p a
  cast (TPst _ p)     = Postfix p

public export
0 Toks : (t,p,i,o : Type) -> Type
Toks t p i o = List (Tok t p i o)

public export
0 Skot : (t,p,i,o : Type) -> Type
Skot t p i o = SnocList (Tok t p i o)

--------------------------------------------------------------------------------
-- Shunting Yard Implementation
--------------------------------------------------------------------------------

parameters {0 t,p,i,o,e : Type}
           {auto cst    : Cast (ShuntingErr i) e}
           (pre         : ByteBounded p -> t -> t)
           (inf         : t -> ByteBounded i -> t -> t)
           (pst         : ByteBounded o -> t -> t)

  0 Res : Type
  Res = Either (ByteBounded e) (Skot t p i o)

  err : ByteBounded i -> Precedence -> Either (ByteBounded e) a
  err op p = Left (B (cast $ AssocNone op.val p) op.bounds)

  app : Tok t p i o -> t -> t
  app (TPre op _)     y = pre op y
  app (TInf x op _ _) y = inf x op y
  app (TPst op _)     y = pst op y

  apply : Skot t p i o -> t -> t
  apply [<]     lst = lst
  apply (si:<i) lst = apply si (app i lst)

  insInf : Skot t p i o -> t -> ByteBounded i -> Nat -> Assoc -> Res
  insInf [<]     lst op n a = Right $ [<TInf lst op n a]
  insInf (si:<i) lst op n a =
    case compare (prec i) n of
      LT => Right $ si:<i:<TInf lst op n a
      GT => insInf si (app i lst) op n a
      EQ =>
       let False := InfixL == a | True => insInf si (app i lst) op n a
           False := None == a   | True => err op $ Infix n a
           TInf _ o _ x := i    | _    => Right $ si:<i:<TInf lst op n a
           False := None == x   | True => err o $ Infix n x
        in Right $ si:<i:<TInf lst op n a

  impl : Skot t p i o -> Toks t p i o -> t -> Either (ByteBounded e) t
  impl si []      lst = Right $ apply si lst
  impl si (i::is) lst =
    case i of
      TPre op n     => impl (si:<TPre op n) is lst
      TInf t op n a => case insInf si t op n a of
        Left err  => Left err
        Right si2 => impl si2 is lst
      TPst op n     => impl (si:<TPst op n) is lst

  ||| An implementation of the
  ||| [shunting yard algorithm](https://en.wikipedia.org/wiki/Shunting_yard_algorithm)
  ||| used to convert term-operator chains such as `1 + 2 * 3 ^ 4` to proper
  ||| syntax trees based on the operators' associativity and precedence.
  export %inline
  shuntingYard : Skot t p i o -> t -> Either (ByteBounded e) t
  shuntingYard = impl [<] . (<>> [])

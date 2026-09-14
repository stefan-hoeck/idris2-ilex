module Shunting.Term

import Derive.Prelude
import public Text.ILex.Shunting

%default total
%language ElabReflection

public export
data Op : Type where
  PLUS  : Op
  MINUS : Op
  TIMES : Op
  EQ    : Op
  LT    : Op
  LTE   : Op
  GT    : Op
  GTE   : Op
  AND   : Op
  OR    : Op
  NEG   : Op
  NOT   : Op

%runElab derive "Op" [Show,Eq]

public export
data Syntax : Type where
  SSeq  : Skot Syntax Op -> Syntax -> Syntax
  SBool : Bool -> Syntax
  SNat  : Nat -> Syntax

%runElab derive "Syntax" [Show,Eq]

export
sseq : Skot Syntax Op -> Syntax -> Syntax
sseq [<] s = s
sseq sk  s = SSeq sk s

public export
Cast Op Precedence where
  cast PLUS  = Infix 8 InfixL
  cast MINUS = Infix 8 InfixL
  cast TIMES = Infix 9 InfixL
  cast EQ    = Infix 6 None
  cast LT    = Infix 6 None
  cast LTE   = Infix 6 None
  cast GT    = Infix 6 None
  cast GTE   = Infix 6 None
  cast AND   = Infix 5 InfixR
  cast OR    = Infix 4 InfixR
  cast NEG   = Prefix 10
  cast NOT   = Prefix 10

public export
data Term : Type where
  TI    : Term -> Op -> Term -> Term
  TP    : Op -> Term -> Term
  TBool : Bool -> Term
  TNat  : Nat -> Term

%runElab derive "Term" [Show,Eq]

skot : Skot Syntax Op -> Either (ShuntingErr Op) (Skot Term Op)

shunt : Syntax -> Either (ShuntingErr Op) Term
shunt (SSeq sk s) = Prelude.do
  skt <- skot sk
  t   <- shunt s
  shuntingYard TI TP skt t
shunt (SBool b)   = Right (TBool b)
shunt (SNat n)    = Right (TNat n)

skot [<] = Right [<]
skot (si:<i) =
  case i of
    TPre o   n   => ?precase
    TInf s o n a => ?infcase

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
  POW   : Op
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
  cast POW   = Infix 10 InfixR
  cast EQ    = Infix 6 None
  cast LT    = Infix 6 None
  cast LTE   = Infix 6 None
  cast GT    = Infix 6 None
  cast GTE   = Infix 6 None
  cast AND   = Infix 5 InfixR
  cast OR    = Infix 4 InfixR
  cast NEG   = Prefix 11
  cast NOT   = Prefix 11

public export
data Term : Type where
  TI    : Term -> Op -> Term -> Term
  TP    : Op -> Term -> Term
  TBool : Bool -> Term
  TNat  : Nat -> Term

%runElab derive "Term" [Show,Eq]

shuntTok : Tok Syntax Op -> Either (ShuntingErr Op) (Tok Term Op)

skot : Toks Term Op -> Skot Syntax Op -> Either (ShuntingErr Op) (Skot Term Op)
skot is [<]     = Right ([<] <>< is)
skot is (si:<i) =
 let Right i2 := shuntTok i | Left x => Left x
  in skot (i2::is) si

export
desugar : Syntax -> Either (ShuntingErr Op) Term
desugar (SSeq sk s) = Prelude.do
  skt <- skot [] sk
  t   <- desugar s
  shuntingYard TI TP skt t
desugar (SBool b)   = Right (TBool b)
desugar (SNat n)    = Right (TNat n)

shuntTok (TPre o n) = Right (TPre o n)
shuntTok (TInf t o n a) =
 let Right s := desugar t | Left x => Left x
  in Right (TInf s o n a)

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

isAtom : Term -> Bool
isAtom (TBool x)  = True
isAtom (TNat k)   = True
isAtom _          = False

prettyOp : Op -> String
prettyOp PLUS  = "+"
prettyOp MINUS = "-"
prettyOp TIMES = "*"
prettyOp POW   = "^"
prettyOp EQ    = "=="
prettyOp LT    = "<"
prettyOp LTE   = "<="
prettyOp GT    = ">"
prettyOp GTE   = ">="
prettyOp AND   = "&&"
prettyOp OR    = "||"
prettyOp NEG   = "-"
prettyOp NOT   = "~"

prettyPar, pretty : Term -> String

pretty (TI x y z) = "\{prettyPar x} \{prettyOp y} \{prettyPar z}"
pretty (TP x y)   = "\{prettyOp x}\{prettyPar y}"
pretty (TBool x)  = toLower (show x)
pretty (TNat k)   = show k

prettyPar v = if isAtom v then pretty v else "(\{pretty v})"

export %inline
Interpolation Term where interpolate = pretty

module Shunting.Term

import Derive.Prelude
import Text.ILex
import public Text.ILex.Shunting

%default total
%language ElabReflection

public export
data IOp : Type where
  PLUS  : IOp
  MINUS : IOp
  TIMES : IOp
  POW   : IOp
  EQ    : IOp
  LT    : IOp
  LTE   : IOp
  GT    : IOp
  GTE   : IOp
  AND   : IOp
  OR    : IOp

%runElab derive "IOp" [Show,Eq]

public export
data POp : Type where
  NEG   : POp
  NOT   : POp

%runElab derive "POp" [Show,Eq]

export
Interpolation IOp where
  interpolate PLUS  = "+"
  interpolate MINUS = "-"
  interpolate TIMES = "*"
  interpolate POW   = "^"
  interpolate EQ    = "=="
  interpolate LT    = "<"
  interpolate LTE   = "<="
  interpolate GT    = ">"
  interpolate GTE   = ">="
  interpolate AND   = "&&"
  interpolate OR    = "||"

export
Interpolation POp where
  interpolate NEG   = "-"
  interpolate NOT   = "~"

public export
data Syntax : Type where
  SSeq  : Skot Syntax POp IOp -> Syntax -> Syntax
  SBool : Bool -> Syntax
  SNat  : Nat -> Syntax

%runElab derive "Syntax" [Show,Eq]

export
sseq : Skot Syntax POp IOp -> Syntax -> Syntax
sseq [<] s = s
sseq sk  s = SSeq sk s

public export
data Term : Type where
  TI    : Term -> IOp -> Term -> Term
  TP    : POp -> Term -> Term
  TBool : Bool -> Term
  TNat  : Nat -> Term

%runElab derive "Term" [Show,Eq]

export
Num Term where
  fromInteger = TNat . cast
  x + y = TI x PLUS y
  x * y = TI x TIMES y

export
Neg Term where
  negate = TP NEG
  x - y  = TI x MINUS y

public export
0 TErr : Type
TErr = BBErr (ShuntingErr IOp)

shuntTok : Tok Syntax POp IOp -> Either TErr (Tok Term POp IOp)

skot :
     Toks Term POp IOp
  -> Skot Syntax POp IOp
  -> Either TErr (Skot Term POp IOp)
skot is [<]     = Right ([<] <>< is)
skot is (si:<i) =
 let Right i2 := shuntTok i | Left x => Left x
  in skot (i2::is) si

export
desugar : Syntax -> Either TErr Term
desugar (SSeq sk s) = Prelude.do
  skt <- skot [] sk
  t   <- desugar s
  shuntingYard (\x,y => TI x y.val) (\x => TP x.val) skt t
desugar (SBool b)   = Right (TBool b)
desugar (SNat n)    = Right (TNat n)

shuntTok (TPre o n) = Right (TPre o n)
shuntTok (TInf t o n a) = (\s => TInf s o n a) <$> desugar t

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

isAtom : Term -> Bool
isAtom (TBool x)  = True
isAtom (TNat k)   = True
isAtom _          = False

prettyPar, pretty : Term -> String

pretty (TI x y z) = "\{prettyPar x} \{y} \{prettyPar z}"
pretty (TP x y)   = "\{x}\{prettyPar y}"
pretty (TBool x)  = toLower (show x)
pretty (TNat k)   = show k

prettyPar v = if isAtom v then pretty v else "(\{pretty v})"

export %inline
Interpolation Term where interpolate = pretty

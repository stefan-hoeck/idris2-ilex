module Shunting.Term

import Derive.Prelude
import Text.ILex
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

export
Interpolation Op where
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
  interpolate NEG   = "-"
  interpolate NOT   = "~"

public export
0 BOp : Type
BOp = ByteBounded Op

public export
data Syntax : Type where
  SSeq  : Skot Syntax BOp -> Syntax -> Syntax
  SBool : Bool -> Syntax
  SNat  : Nat -> Syntax

%runElab derive "Syntax" [Show,Eq]

export
sseq : Skot Syntax BOp -> Syntax -> Syntax
sseq [<] s = s
sseq sk  s = SSeq sk s

public export
data Term : Type where
  TI    : Term -> BOp -> Term -> Term
  TP    : BOp -> Term -> Term
  TBool : Bool -> Term
  TNat  : Nat -> Term

%runElab derive "Term" [Show,Eq]

export
MapBounds Term where
  mapBounds f (TI x y z) = TI (mapBounds f x) (mapBounds f y) (mapBounds f z)
  mapBounds f (TP x y)   = TP (mapBounds f x) (mapBounds f y)
  mapBounds f t          = t

public export
0 TErr : Type
TErr = BBErr (ShuntingErr Op)

toErr : ShuntingErr BOp -> TErr
toErr (AssocNone bo p) = B (Custom $ AssocNone bo.val p) bo.bounds

shuntTok : Tok Syntax BOp -> Either TErr (Tok Term BOp)

skot : Toks Term BOp -> Skot Syntax BOp -> Either TErr (Skot Term BOp)
skot is [<]     = Right ([<] <>< is)
skot is (si:<i) =
 let Right i2 := shuntTok i | Left x => Left x
  in skot (i2::is) si

export
desugar : Syntax -> Either TErr Term
desugar (SSeq sk s) = Prelude.do
  skt <- skot [] sk
  t   <- desugar s
  mapFst toErr $ shuntingYard TI TP skt t
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

prettyPar, pretty : Term -> String

pretty (TI x y z) = "\{prettyPar x} \{y.val} \{prettyPar z}"
pretty (TP x y)   = "\{x.val}\{prettyPar y}"
pretty (TBool x)  = toLower (show x)
pretty (TNat k)   = show k

prettyPar v = if isAtom v then pretty v else "(\{pretty v})"

export %inline
Interpolation Term where interpolate = pretty

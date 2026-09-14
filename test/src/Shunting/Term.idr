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
  SSeq  : SnocList (Either Syntax Op) -> Syntax
  SBool : Bool -> Syntax
  SInt  : Integer -> Syntax

%runElab derive "Syntax" [Show,Eq]

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

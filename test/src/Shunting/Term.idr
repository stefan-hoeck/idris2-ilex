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

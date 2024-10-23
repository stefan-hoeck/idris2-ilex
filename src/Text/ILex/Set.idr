module Text.ILex.Set

import Derive.Prelude
import Derive.Pretty
import Text.ILex.Val

%default total
%language ElabReflection

public export
0 VPred : Type
VPred = Val (Char -> Bool)

public export
predTpe : TOnly (Char -> Bool)
predTpe = funType2 Char Bool

||| Different encodings for the concept of a *set of characters*
public export
data Set : Type where
  ||| Matches exactly the given character
  Chr   : Char -> Set

  Pred  : VPred -> Set

  ||| Matches every character except '\n'
  Any   : Set

%runElab derive "Set" [Show,Eq,Ord,Pretty]

public export
data Rule : Type where
  Eps : Rule
  A   : Rule
  C   : Char -> Rule
  P   : VPred -> Rule

%runElab derive "Rule" [Show,Eq,Ord]

public export
fromSet : Set -> Rule
fromSet (Chr c)  = C c
fromSet (Pred p) = P p
fromSet Any      = A

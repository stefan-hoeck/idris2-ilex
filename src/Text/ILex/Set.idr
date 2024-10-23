module Text.ILex.Set

import Derive.Prelude
import Derive.Pretty

%default total
%language ElabReflection

||| Different encodings for the concept of a *set of characters*
public export
data Set : Type where
  ||| Matches exactly the given character
  Chr   : Char -> Set

  ||| Matches a range of characters
  Range : Char -> Char -> Set

  ||| Matches every character except '\n'
  Dot   : Set

%runElab derive "Set" [Show,Eq,Ord,Pretty]

public export
data Rule : Type where
  Eps : Rule
  C   : Char -> Rule
  R   : Char -> Char -> Rule
  D   : Rule

%runElab derive "Rule" [Show,Eq,Ord]

public export
fromSet : Set -> Rule
fromSet (Chr c)     = C c
fromSet (Range c d) = R c d
fromSet Dot         = D

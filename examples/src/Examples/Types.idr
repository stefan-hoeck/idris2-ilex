module Examples.Types

import Data.ByteString
import Derive.Prelude

%default total
%language ElabReflection

public export
data AorB : Type where
  A : AorB
  B : AorB

%runElab derive "AorB" [Show,Eq]

public export
data Expr : Type where
  Lit  : Nat -> Expr
  Plus : Expr
  Mult : Expr
  PO   : Expr
  PC   : Expr

%runElab derive "Expr" [Show,Eq]

export
toNat : ByteString -> Expr

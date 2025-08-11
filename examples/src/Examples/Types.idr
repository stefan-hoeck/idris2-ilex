module Examples.Types

import Text.PrettyPrint.Bernardy
import Data.ByteString
import Derive.Prelude

%default total
%language ElabReflection

public export
data AorB : Type where
  A : AorB
  B : AorB

%runElab derive "AorB" [Show,Eq]

export
Interpolation AorB where interpolate = show

export
Pretty AorB where prettyPrec p = line . interpolate

public export
data Op = P | S | M | X

%runElab derive "Op" [Show,Eq]

prio : Op -> Nat
prio P = 0
prio S = 0
prio M = 1
prio X = 2

export %inline
Ord Op where compare = compare `on` prio

export
Interpolation Op where
  interpolate P = "+"
  interpolate S = "-"
  interpolate M = "*"
  interpolate X = "^"

public export
data Expr : Type where
  Lit   : Integer -> Expr
  Bin   : Op -> Expr -> Expr -> Expr

%runElab derive "Expr" [Show,Eq]

export
Interpolation Expr where
  interpolate (Lit n)     = show n
  interpolate (Bin o x y) = "(\{x} \{o} \{y})"

public export
data TExpr : Type where
  TLit : Integer -> TExpr
  TOp  : Op -> TExpr
  PO   : TExpr
  PC   : TExpr

%runElab derive "TExpr" [Show,Eq]

export
Interpolation TExpr where
  interpolate (TLit k) = show k
  interpolate (TOp x)  = interpolate x
  interpolate PO       = "'('"
  interpolate PC       = "')'"

export
Pretty TExpr where prettyPrec p = line . interpolate

export
toNat : ByteString -> TExpr
toNat = TLit . cast . toString

public export
data Ident : Type where
  Id   : String -> Ident
  Else : Ident

%runElab derive "Ident" [Show,Eq]

export
Interpolation Ident where interpolate = show

export
Pretty Ident where prettyPrec p = line . interpolate

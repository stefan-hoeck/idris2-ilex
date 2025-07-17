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

export
Interpolation AorB where interpolate = show

public export
data Op = P | M | X

%runElab derive "Op" [Show,Eq,Ord]

public export
data Expr : Type where
  Lit  : Nat -> Expr
  Plus : Expr -> Expr -> Expr
  Mult : Expr -> Expr -> Expr
  Exp  : Expr -> Expr -> Expr

%runElab derive "Expr" [Show,Eq]

export
Interpolation Expr where
  interpolate (Lit n) = show n
  interpolate (Plus x y) = "(\{x} + \{y})"
  interpolate (Mult x y) = "(\{x} * \{y})"
  interpolate (Exp  x y) = "(\{x} ^ \{y})"

public export
data TExpr : Type where
  TLit : Nat -> TExpr
  TOp  : Op -> TExpr
  PO   : TExpr
  PC   : TExpr

%runElab derive "TExpr" [Show,Eq]

export
Interpolation TExpr where interpolate = show

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
decNat : ByteString -> Integer
decNat (BS n bv) = go 0 n
  where
    go : Integer -> (k : Nat) -> (x : Ix k n) => Integer
    go res 0     = res
    go res (S k) = go (res * 10 + cast (ix bv k) - 48) k

public export
data JSON : Type where
  Null   : JSON
  JBool  : Bool -> JSON
  JStr   : String -> JSON
  JNum   : Double -> JSON
  JInt   : Integer -> JSON
  JPO    : JSON
  JPC    : JSON
  JBO    : JSON
  JBC    : JSON
  JComma : JSON
  JColon : JSON

%runElab derive "JSON" [Show,Eq]

export
Interpolation JSON where interpolate = show

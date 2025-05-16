module Examples.Types

import Data.ByteString
import Derive.Prelude

%default total
%language ElabReflection

public export
data AorB : Type where
  A : AorB
  B : AorB
  E : AorB -- end of input

%runElab derive "AorB" [Show,Eq]

public export
data Expr : Type where
  Lit  : Nat -> Expr
  Plus : Expr
  Mult : Expr
  PO   : Expr
  PC   : Expr
  EE   : Expr -- end of input

%runElab derive "Expr" [Show,Eq]

export
toNat : ByteString -> Expr

public export
data Ident : Type where
  Id   : String -> Ident
  Else : Ident
  IE   : Ident -- end of input

%runElab derive "Ident" [Show,Eq]

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
  JEOI   : JSON

%runElab derive "JSON" [Show,Eq]

module Text.ILex.RExp

import Data.ByteString
import public Text.ILex.Char.Set
import public Text.ILex.Val
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Regular Expressions
--------------------------------------------------------------------------------

||| A data type for regular expressions.
|||
||| The `Bool` flag indicates, if the regular expression consumes
||| at least one character of input or not.
public export
data RExpOf : Bool -> Type -> Type where
  Eps  : RExpOf False t
  Ch   : SetOf t -> RExpOf True t
  And  : RExpOf b1 t -> RExpOf b2 t -> RExpOf (b1 || b2) t
  Or   : RExpOf b1 t -> RExpOf b2 t -> RExpOf (b1 && b2) t
  Star : RExpOf True t -> RExpOf False t

%runElab derivePattern "RExpOf" [I,P] [Show]

public export
0 RExp : Bool -> Type
RExp b = RExpOf b Bits32

public export
0 RExp8 : Bool -> Type
RExp8 b = RExpOf b Bits8

public export
data IsCh : RExpOf b t -> Type where
  ItIsCh : IsCh (Ch s)

export
adjRanges : (SetOf t -> RExpOf True s) -> RExpOf b t -> RExpOf b s
adjRanges f Eps       = Eps
adjRanges f (Ch x)    = f x
adjRanges f (And x y) = And (adjRanges f x) (adjRanges f y)
adjRanges f (Or x y)  = Or (adjRanges f x) (adjRanges f y)
adjRanges f (Star x)  = Star (adjRanges f x)

--------------------------------------------------------------------------------
-- Conv
--------------------------------------------------------------------------------

public export
data Conv : Type -> Type where
  Ignore : Conv a
  Const  : Val a -> Conv a
  Txt    : Val (ByteString -> a) -> Conv a
  Chr    : Val (Bits8 -> a) -> Conv a
  Len    : Val (Nat -> a) -> Conv a

export
Eq (Conv a) where
  Ignore   == Ignore   = True
  Const v1 == Const v2 = v1 == v2
  Txt   v1 == Txt v2   = v1 == v2
  Len   v1 == Len v2   = v1 == v2
  Chr   v1 == Chr v2   = v1 == v2
  _        == _        = False

export
Show (Conv a) where
  showPrec p Ignore    = "Ignore"
  showPrec p (Const x) = showCon p "Const" (showArg x)
  showPrec p (Txt x)   = showCon p "Txt" (showArg x)
  showPrec p (Len x)   = showCon p "Len" (showArg x)
  showPrec p (Chr x)   = showCon p "Chr" (showArg x)

export %macro
const : (0 x : a) -> Elab (Conv a)
const x = do
  v <- lift x
  pure (Const v)

export %macro
bytes : (0 x : ByteString -> a) -> Elab (Conv a)
bytes x = do
  v <- lift x
  pure (Txt v)

export %macro
char : (0 x : Bits8 -> a) -> Elab (Conv a)
char x = do
  v <- lift x
  pure (Chr v)

export %macro
count : (0 x : Nat -> a) -> Elab (Conv a)
count x = do
  v <- lift x
  pure (Len v)

public export
0 TokenMap : Type -> Type
TokenMap a = List (RExp True, Conv a)

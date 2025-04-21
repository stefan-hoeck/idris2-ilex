module Text.ILex.Val

import Derive.Prelude
import Derive.Pretty
import Language.Reflection.Pretty
import Language.Reflection.Util

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Basic Types
--------------------------------------------------------------------------------

||| Basic Idris data types
public export
data Tpe : Type where
  Plain : String -> Tpe
  App   : Tpe -> Tpe -> Tpe
  NApp  : Tpe -> String -> Tpe -> Tpe
  Prim  : PrimType -> Tpe
  Pi    : Tpe -> Tpe -> Tpe
  Ty    : Tpe

public export
FromString Tpe where
  fromString = Plain

%runElab derive "PrimType" [ConIndex,Ord]
%runElab derive "Tpe" [Eq,Ord]

public export
toName : Name -> Maybe String
toName (NS _ n)       = toName n
toName (MN s n)       = Just "\{s}\{show n}"
toName (UN $ Basic n) =
  case strM n of
    StrNil         => Just n
    (StrCons x xs) => if isAlpha x then Just n else Just "(\{n})"
toName (DN n _) =
  case strM n of
    StrNil         => Just n
    (StrCons x xs) => if isAlpha x then Just n else Just "(\{n})"
toName _              = Nothing

public export
toTpe : TTImp -> Maybe Tpe
toTpe (IVar _ nm)                 = Plain <$> toName nm
toTpe (IApp _ s t)                = [| App (toTpe s) (toTpe t) |]
toTpe (INamedApp _ s nm t)        = [| NApp (toTpe s) (toName nm) (toTpe t) |]
toTpe (IPrimVal _ $ PrT c)        = Just $ Prim c
toTpe (IType _)                   = Just Ty
toTpe (IPi _ MW ExplicitArg n s t) = [| Pi (toTpe s) (toTpe t) |]
toTpe (IPi _ c _ n s t)           = toTpe t
toTpe _                           = Nothing

app : Nat -> String -> String
app 0 s = s
app 1 s = s
app _ s = "(\{s})"

pi : Nat -> String -> String
pi 0 s = s
pi _ s = "(\{s})"

printPrimType : PrimType -> String
printPrimType IntType     = "Int"
printPrimType IntegerType = "Integer"
printPrimType Int8Type    = "Int8"
printPrimType Int16Type   = "Int16"
printPrimType Int32Type   = "Int32"
printPrimType Int64Type   = "Int64"
printPrimType Bits8Type   = "Bits8"
printPrimType Bits16Type  = "Bits16"
printPrimType Bits32Type  = "Bits32"
printPrimType Bits64Type  = "Bits64"
printPrimType StringType  = "String"
printPrimType CharType    = "Char"
printPrimType DoubleType  = "Double"
printPrimType WorldType   = "%World"

printTpePrec : Nat -> Tpe -> String
printTpePrec p (Plain str)    = str
printTpePrec p (App x y)      =
  app p "\{printTpePrec 0 x} \{printTpePrec 2 y}"
printTpePrec p (NApp x s y) =
  app p "\{printTpePrec 0 x} {\{s} = \{printTpePrec 0 y}}"
printTpePrec p (Prim pty)     = printPrimType pty
printTpePrec p (Pi x y)       =
  pi p "\{printTpePrec 1 x} -> \{printTpePrec 0 y}"
printTpePrec p Ty             = "Type"

export
Show Tpe where
  showPrec Open = printTpePrec 0
  showPrec _    = printTpePrec 2

export
Pretty Tpe where
  prettyPrec p = line . showPrec p

export %inline
Interpolation Tpe where
  interpolate = show

export
piAll : (res : Tpe) -> List Tpe -> Tpe
piAll res []        = res
piAll res (x :: xs) = Pi x (piAll res xs)

--------------------------------------------------------------------------------
-- Basic Values
--------------------------------------------------------------------------------

public export
data Value : Type where
  VPlain : String -> Value
  VApp   : Value -> Value -> Value
  VNApp  : Value -> String -> Value -> Value
  VLam   : String -> Value -> Value
  VPrim  : Constant -> Value

public export
FromString Value where
  fromString = VPlain

public export
FromChar Value where
  fromChar = VPrim . Ch

%runElab derive "Constant" [Ord]
%runElab derive "Value" [Eq,Ord]

public export
toVal : TTImp -> Maybe Value
toVal (IVar _ nm)          = VPlain <$> toName nm
toVal (ILam _ _ _ mnm _ t) =
  maybe (toVal t) (\n => VLam n <$> toVal t) (mnm >>= toName)
toVal (IApp _ s t)         = [| VApp (toVal s) (toVal t) |]
toVal (INamedApp _ s nm t) = toVal s
toVal (IAutoApp _ s t)     = toVal s
toVal (IDelayed _ _ s)     = toVal s
toVal (IDelay _ s)         = toVal s
toVal (IForce _ s)         = toVal s
toVal (IPrimVal _ c)       = Just $ VPrim c
toVal _                    = Nothing

public export
value : (t : TTImp) -> (0 p : IsJust (toVal t)) => Value
value t = fromJust $ toVal t

public export
appAll : Value -> List Value -> Value
appAll v []        = v
appAll v (x :: xs) = appAll (VApp v x) xs

showNeg : Ord t => Num t => Neg t => Show t => t -> String
showNeg x = if x < 0 then "(\{show x})" else show x

printConst : Constant -> String
printConst (I i)    = showNeg i
printConst (BI i)   = showNeg i
printConst (I8 i)   = showNeg i
printConst (I16 i)  = showNeg i
printConst (I32 i)  = showNeg i
printConst (I64 i)  = showNeg i
printConst (B8 m)   = show m
printConst (B16 m)  = show m
printConst (B32 m)  = show m
printConst (B64 m)  = show m
printConst (Str s)  = show s
printConst (Ch c)   = show c
printConst (Db d)   = showNeg d
printConst (PrT p)  = printPrimType p
printConst WorldVal = "%MkWorld"

printValPrec : Nat -> Value -> String
printValPrec p (VPlain s) = s
printValPrec p (VApp x y) =
  app p "\{printValPrec 0 x} \{printValPrec 2 y}"
printValPrec p (VNApp x s y) =
  app p "\{printValPrec 0 x} {\{s} = \{printValPrec 0 y}}"
printValPrec p (VLam s x) = app p "\\\{s} => \{printValPrec 0 x}"
printValPrec p (VPrim c)  = printConst c

export
Show Value where
  showPrec Open = printValPrec 0
  showPrec _    = printValPrec 2

export
Pretty Value where
  prettyPrec p = line . showPrec p

--------------------------------------------------------------------------------
-- Normalize Values
--------------------------------------------------------------------------------

replace : String -> Value -> Value -> Value
replace s x (VPlain n)    = if s == n then x else VPlain n
replace s x (VApp y z)    = VApp (replace s x y) (replace s x z)
replace s x (VNApp y n z) = VNApp (replace s x y) n (replace s x z)
replace s x (VLam n y)    =
  if n /= s then VLam n (replace s x y) else VLam n y
replace s x (VPrim c)     = VPrim c

export
toNF : Value -> Value
toNF (VApp x y) =
  let vy := toNF y
      vx := toNF x
   in case vx of
        VLam s v => toNF (assert_smaller x $ replace s vy v)
        v        => VApp vx vy
toNF v          = v

export %inline
Interpolation Value where
  interpolate = show . toNF

--------------------------------------------------------------------------------
-- Types Only
--------------------------------------------------------------------------------

public export
record TOnly (a : Type) where
  constructor TO
  tpe : Tpe

%runElab derive "TOnly" [Show,Eq,Ord]

export %inline
Pretty (TOnly a) where
  prettyPrec p = prettyPrec p . tpe

public export
interface ToType a where
  toType_ : TOnly a

public export %inline
toType : (0 a : Type) -> ToType a => TOnly a
toType _ = toType_

public export %inline
tpeof : (0 a : Type) -> ToType a => Tpe
tpeof a = tpe $ toType a

public export %inline
ToType Integer where
  toType_ = TO (Prim IntegerType)

public export %inline
ToType Int where
  toType_ = TO (Prim IntType)

public export %inline
ToType Int8 where
  toType_ = TO (Prim Int8Type)

public export %inline
ToType Int16 where
  toType_ = TO (Prim Int16Type)

public export %inline
ToType Int32 where
  toType_ = TO (Prim Int32Type)

public export %inline
ToType Int64 where
  toType_ = TO (Prim Int64Type)

public export %inline
ToType Bits8 where
  toType_ = TO (Prim Bits8Type)

public export %inline
ToType Bits16 where
  toType_ = TO (Prim Bits16Type)

public export %inline
ToType Bits32 where
  toType_ = TO (Prim Bits32Type)

public export %inline
ToType Bits64 where
  toType_ = TO (Prim Bits64Type)

public export %inline
ToType String where
  toType_ = TO (Prim StringType)

public export %inline
ToType Char where
  toType_ = TO (Prim CharType)

public export %inline
ToType a => ToType (Maybe a) where
  toType_ = TO (App "Maybe" (tpeof a))

public export %inline
ToType a => ToType (List a) where
  toType_ = TO (App "List" (tpeof a))

public export %inline
ToType a => ToType (SnocList a) where
  toType_ = TO (App "SnocList" (tpeof a))

public export %inline
ToType a => ToType b => ToType (Either a b) where
  toType_ = TO (App (App "Either" (tpeof a)) (tpeof b))

public export %inline
ToType a => ToType b => ToType (Pair a b) where
  toType_ = TO (App (App "Pair" (tpeof a)) (tpeof b))

public export %inline
ToType Bool where
  toType_ = TO "Bool"

public export %inline
ToType Nat where
  toType_ = TO "Nat"

export
tlift : (0 a : Type) -> Elab (TOnly a)
tlift a = do
  t <- quote a
  Just tp <- pure (toTpe t) | Nothing => failAt EmptyFC "Can't reflect type"
  pure (TO tp)

export %macro
mtlift : (0 a : Type) -> Elab (TOnly a)
mtlift = tlift

public export
funType2 : (0 a,b : Type) -> ToType a => ToType b => TOnly (a -> b)
funType2 a b = TO (Pi (tpeof a) (tpeof b))

public export
funType3 : (0 a,b,c : Type) -> ToType a => ToType b => ToType c => TOnly (a -> b -> c)
funType3 a b c = TO (piAll (tpeof c) [tpeof a, tpeof b])

public export
funType4 : (0 a,b,c,d : Type) -> ToType a => ToType b =>  ToType c => ToType d => TOnly (a -> b -> c -> d)
funType4 a b c d = TO (piAll (tpeof d) [tpeof a, tpeof b, tpeof c])

--------------------------------------------------------------------------------
-- Elaborated Values
--------------------------------------------------------------------------------

public export
record Val (a : Type) where
  constructor V
  tpe : TOnly a
  val : Value

%runElab deriveIndexed "Val" [Show,Eq,Pretty,Ord]

export
lift : (0 x : a) -> Elab (Val a)
lift x = do
  t <- quote a
  Just tp <- pure (toTpe t)
    | Nothing => failAt EmptyFC "Can't reflect type \{show t}"
  v <- quote x
  Just vl <- pure (toVal v)
    | Nothing => failAt EmptyFC "Can't reflect value \{show v}"
  pure (V (TO tp) vl)

export %macro
mlift : (0 x : a) -> Elab (Val a)
mlift = lift

export
vwrap : ToType a => Val (a -> SnocList a)
vwrap = V (funType2 a (SnocList a)) (value `(\x => [<x]))

export
vsnoc : ToType a => Val (SnocList a -> a -> SnocList a)
vsnoc = V (funType3 (SnocList a) a (SnocList a)) "(:<)"

export
vpack : ToType a => Val (SnocList a -> String)
vpack = V (funType2 (SnocList a) String) (value `(\x => pack (x <>> [])))

public export
vjust : ToType a => Val (a -> Maybe a)
vjust = V (funType2 a (Maybe a)) "Just"

public export
vnothing : ToType a => Val (Maybe a)
vnothing = V (toType (Maybe a)) "Nothing"

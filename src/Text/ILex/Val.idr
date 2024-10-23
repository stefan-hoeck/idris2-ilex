module Text.ILex.Val

import Derive.Prelude
import Derive.Pretty
import Language.Reflection.Pretty
import Language.Reflection.Util
import Text.ILex.Util

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Basic Types
--------------------------------------------------------------------------------

public export
data Tpe : Type where
  Plain : String -> Tpe
  App   : Tpe -> Tpe -> Tpe
  NApp  : Tpe -> String -> Tpe -> Tpe
  Prim  : PrimType -> Tpe
  Pi    : Tpe -> Tpe -> Tpe
  Ty    : Tpe

%runElab derive "PrimType" [ConIndex,Ord]
%runElab derive "Tpe" [Eq,Pretty,Ord]

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

%runElab derive "Constant" [Ord]
%runElab derive "Value" [Eq,Pretty,Ord]

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

printConst : Constant -> String
printConst (I i)    = show i
printConst (BI i)   = show i
printConst (I8 i)   = show i
printConst (I16 i)  = show i
printConst (I32 i)  = show i
printConst (I64 i)  = show i
printConst (B8 m)   = show m
printConst (B16 m)  = show m
printConst (B32 m)  = show m
printConst (B64 m)  = show m
printConst (Str s)  = show s
printConst (Ch c)   = show c
printConst (Db d)   = show d
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

%runElab derive "TOnly" [Show,Eq,Pretty,Ord]

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
  toType_ = TO (App (Plain "Maybe") (tpeof a))

public export %inline
ToType a => ToType (List a) where
  toType_ = TO (App (Plain "List") (tpeof a))

public export %inline
ToType a => ToType (SnocList a) where
  toType_ = TO (App (Plain "SnocList") (tpeof a))

public export %inline
ToType a => ToType b => ToType (Either a b) where
  toType_ = TO (App (App (Plain "Either") (tpeof a)) (tpeof b))

public export %inline
ToType a => ToType b => ToType (Pair a b) where
  toType_ = TO (App (App (Plain "Pair") (tpeof a)) (tpeof b))

public export %inline
ToType Bool where
  toType_ = TO (Plain "Bool")

public export %inline
ToType Nat where
  toType_ = TO (Plain "Nat")

public export %inline
ToType LexErr where
  toType_ = TO (Plain "LexErr")

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
charVal : Val Char
charVal = V toType_ (VPlain "c")

export
vunexpected : Val (Char -> LexErr)
vunexpected = mlift Unexpected

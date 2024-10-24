module Text.ILex.Args

import Derive.Prelude
import Derive.Pretty
import Language.Reflection.Util
import Text.ILex.Util
import public Text.ILex.Val

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Argument Lists
--------------------------------------------------------------------------------

namespace Types
  ||| The types of function arguments in snoclist order
  public export
  data Types : Type where
    Lin  : Types
    (:<) : Types -> (0 t : Type) -> Types

namespace LTypes
  ||| The types of function arguments in list order
  public export
  data LTypes : Type where
    Nil  : LTypes
    (::) : (0 t : Type) -> LTypes -> LTypes

  public export
  (<><) : Types -> LTypes -> Types
  (<><) st []       = st
  (<><) st (t :: x) = (st :< t) <>< x

public export
0 Fun : LTypes -> Type -> Type
Fun []      r = r
Fun (t::ts) r = t -> Fun ts r

||| Position in a list of arguments
public export
data Pos : Types -> Type -> Type where
  Lst : Pos (st:<t) t
  Pre : Pos st t -> Pos (st:<u) t

public export
posToNat : Pos is t -> Nat
posToNat Lst     = 0
posToNat (Pre x) = S $ posToNat x

--------------------------------------------------------------------------------
-- Computations with  Argument Lists
--------------------------------------------------------------------------------

||| A computation making use of a subset of a list of function arguments
||| resulting in a value of the given type.
public export
data Conversion : (st : Types) -> Type -> Type where
  ||| Pass the argument at the given position
  CAt   : Pos st t     -> Conversion st t

  ||| Apply a function to a value
  CApp  : Conversion st (a -> b) -> Conversion st a -> Conversion st b

  ||| Lifts a pure value (not a function argument) to be used
  ||| in a computation
  CPure : Val a        -> Conversion st a

  ||| The character we currently match on
  CChar : Conversion st Char

  ||| The current row position
  CRow : Conversion st Nat

  ||| The current column position
  CCol : Conversion st Nat

||| Adjusts a computation so that it can operate on additional values
export
weakenConv : Conversion st t -> Conversion (st:<s) t
weakenConv (CAt x)    = CAt (Pre x)
weakenConv (CApp x y) = CApp (weakenConv x) (weakenConv y)
weakenConv (CPure x)  = CPure x
weakenConv CChar      = CChar
weakenConv CRow       = CRow
weakenConv CCol       = CCol

||| A conversion that consmes all the arguments given in `ts`.
public export
convAll : (ts : LTypes) -> Val (Fun ts r) -> Conversion (is <>< ts) r
convAll ts v = go ts (CPure v)
  where
    pos : (ys : LTypes) -> Pos st y -> Pos (st <>< ys) y
    pos []       p = p
    pos (_ :: x) p = pos x (Pre p)

    go : (us : LTypes) -> Conversion (st <>< us) (Fun us r) -> Conversion (st <>< us) r
    go []        c = c
    go (y :: ys) c = go ys (CApp c (CAt $ pos ys Lst))

||| A list of conversions from one set of function arguments `is`
||| to another set
public export
data Conversions : (is,os : Types) -> Type where
  CID     : Conversions is is
  CWeaken : Conversions is os -> Conversions (is:<i) os
  (:<)    : Conversions is os -> Conversion is o -> Conversions is (os:<o)

||| Appends a converion that maps the last function argument by
||| applying it to the given function value.
export
mapConvs : Val (a -> b) -> Conversions (is:<a) (is:<b)
mapConvs x = CWeaken CID :< CApp (CPure x) (CAt Lst)

export
pureConvs : Val a -> Conversions is (is:<a)
pureConvs x = CID :< CPure x

||| Appends a converion that applies the last two function arguments
||| to the given function value.
export
appConvs : Val (a -> b -> c) -> Conversions (is:<a:<b) (is:<c)
appConvs x =
  CWeaken (CWeaken CID) :< CApp (CApp (CPure x) (CAt $ Pre Lst)) (CAt Lst)

||| Appends a argument to the list of inputs and outputs.
export
appendConv : Conversions is os -> Conversions (is:<t) (os:<t)
appendConv sc = CWeaken sc :< CAt Lst

||| Drops the last argument
export
appendChar : Conversions is (is:<Char)
appendChar = CID :< CChar

export
flipLast : Conversions (is:<a:<s) (is:<s:<a)
flipLast = CWeaken (CWeaken CID) :< CAt Lst :< CAt (Pre Lst)

public export
convsAll : (ts : LTypes) -> Val (Fun ts r) -> Conversions (is <>< ts) (is:<r)
convsAll ts v = weakenBy ts CID :< convAll ts v
  where
    weakenBy : (us : LTypes) -> Conversions xs is -> Conversions (xs <>< us) is
    weakenBy []        x = x
    weakenBy (_ :: ys) x = weakenBy ys (CWeaken x)

--------------------------------------------------------------------------------
-- Untyped Arguments
--------------------------------------------------------------------------------

public export
0 UArgs : Type
UArgs = SnocList Tpe

||| Flips the last function argument types
export
flipArgs : UArgs -> UArgs
flipArgs (sa:<x:<y) = (sa:<y:<x)
flipArgs sa         = sa

lookupTpe : UArgs -> Nat -> Tpe
lookupTpe (sa :< t) 0     = t
lookupTpe (sa :< t) (S y) = lookupTpe sa y
lookupTpe [<]       _     = tpeof Char

||| A computation making use of a subset of a list of function arguments
||| resulting in a value of the given type.
public export
data UConversion : Type where
  ||| Pass the argument at the given position
  UAt   : Nat-> UConversion

  ||| Apply a function to a value
  UApp  : UConversion -> UConversion -> UConversion

  ||| Lifts a pure value (not a function argument) to be used
  ||| in a computation
  UPure : Tpe -> Value -> UConversion

  ||| The character we currently match on
  UChar : UConversion

  ||| The current row position
  URow  : UConversion

  ||| The current column position
  UCol  : UConversion

export
convToVal : UConversion -> Value
convToVal (UAt k)     = VPlain "x\{show k}"
convToVal (UApp x y)  = VApp (convToVal x) (convToVal y)
convToVal (UPure x y) = y
convToVal UChar       = "c"
convToVal URow        = "row"
convToVal UCol        = "col"

%runElab derive "UConversion" [Eq]

export %inline
Show UConversion where
  showPrec p = showPrec p . toNF . convToVal

export %inline
Pretty UConversion where
  prettyPrec p = line . showPrec p

export
uconv : Conversion is o -> UConversion
uconv (CAt p)    = UAt (posToNat p)
uconv (CApp x y) = UApp (uconv x) (uconv y)
uconv (CPure v)  = UPure v.tpe.tpe v.val
uconv CChar      = UChar
uconv CRow       = URow
uconv CCol       = UCol

public export
0 UConversions : Type
UConversions = SnocList UConversion

outType : Tpe -> Tpe
outType (Pi _ y) = y
outType x        = x

export
outArg : UArgs -> UConversion -> Tpe
outArg args (UAt x)     = lookupTpe args x
outArg args (UApp x y)  = outType $ outArg args x
outArg args (UPure x _) = x
outArg args UChar       = tpeof Char
outArg args URow        = tpeof Nat
outArg args UCol        = tpeof Nat

public export
data TTypes : Types -> Type where
  TZ : TTypes [<]
  TS : TTypes is -> TTypes (is:<i)

export
fromTypes : Nat -> TTypes is -> UConversions
fromTypes _ TZ     = [<]
fromTypes n (TS k) = fromTypes (S n) k :< UAt n

export
appendChr : TTypes is -> UConversions
appendChr ts = fromTypes 0 ts :< uconv {is = [<]} CChar

weaken : UConversion -> UConversion
weaken (UAt k)     = UAt (S k)
weaken (UApp x y)  = UApp (weaken x) (weaken y)
weaken (UPure x y) = UPure x y
weaken UChar       = UChar
weaken URow        = URow
weaken UCol        = UCol

export
uconvs : TTypes is -> Conversions is os -> (UConversions, TTypes os)
uconvs ti      CID         = (fromTypes 0 ti, ti)
uconvs (TS ti) (CWeaken x) =
  let (uc, to) := uconvs ti x
   in (map weaken uc, to)
uconvs ti (x :< y)         =
  let (uc, to) := uconvs ti x
   in (uc :< uconv y, TS to)

export
lookup : UConversions -> Nat -> UConversion
lookup (_ :< c) 0     = c
lookup (x :< _) (S k) = lookup x k
lookup [<]      n     = UAt n -- impossible

export
adapt : UConversions -> UConversion -> UConversion
adapt xs (UAt x)     = lookup xs x
adapt xs (UApp x y)  = UApp (adapt xs x) (adapt xs y)
adapt xs (UPure x y) = (UPure x y)
adapt xs UChar       = UChar
adapt xs URow        = URow
adapt xs UCol        = UCol

||| Merges to argument list conversions so that the output functions
||| operate directly on the previous input list
export
merge : UConversions -> UConversions -> UConversions
merge xs [<]       = [<]
merge xs (sc :< c) = merge xs sc :< adapt xs c

public export
data Conv : Type where
  ID : Conv
  UC : UConversions -> Conv
  EC : UConversions -> Conv

%runElab derive "Conv" [Show,Eq,Pretty]

export
trans : Conv -> Conv -> Conv
trans ID     c      = c
trans c      ID     = c
trans (UC x) (UC y) = UC $ merge x y
trans (UC x) (EC y) = EC $ merge x y
trans (EC x) _      = EC x

export
outArgs : UArgs -> Conv -> Maybe UArgs
outArgs args ID     = Just args
outArgs args (UC c) = Just $ map (outArg args) c
outArgs args (EC c) = Nothing

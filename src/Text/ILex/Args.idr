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
  ||| The types of function arguments
  public export
  data Types : Type where
    Lin  : Types
    (:<) : Types -> (0 t : Type) -> Types

||| Position in a list of arguments
public export
data Pos : Types -> Type -> Type where
  Lst : Pos (st:<t) t
  Pre : Pos st t -> Pos (st:<u) t

public export
posToNat : Pos is t -> Nat
posToNat Lst     = 0
posToNat (Pre x) = S $ posToNat x

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

||| Adjusts a computation so that it can operate on additional values
export
weakenConv : Conversion st t -> Conversion (st:<s) t
weakenConv (CAt x)    = CAt (Pre x)
weakenConv (CApp x y) = CApp (weakenConv x) (weakenConv y)
weakenConv (CPure x)  = CPure x

namespace Conversions
  ||| A list of conversions from one set of function arguments `is`
  ||| to another set
  public export
  data Conversions : (is,os : Types) -> Type where
    Lin  : Conversions is [<]
    (:<) : Conversions is os -> (c : Conversion is o) -> Conversions is (os:<o)

||| Adjusts a conversion so that it can operate on additional values
export
weakenConvs : Conversions is os -> Conversions (is:<i) os
weakenConvs [<]       = [<]
weakenConvs (sc :< c) = weakenConvs sc :< weakenConv c

||| Converts a list of function arguments to a list of conversions that
||| just pass on the arguments.
export
fromTypes : {is : Types} -> Conversions is is
fromTypes {is = [<]}     = [<]
fromTypes {is = (si:<i)} = weakenConvs fromTypes :< CAt Lst

||| Appends a converion that maps the last function argument by
||| applying it to the given function value.
export
mapConvs : {is : Types} -> Val (a -> b) -> Conversions (is:<a) (is:<b)
mapConvs x = weakenConvs fromTypes :< CApp (CPure x) (CAt Lst)

export
pureConvs : {is : Types} -> Val a -> Conversions is (is:<a)
pureConvs x = fromTypes :< CPure x

||| Appends a converion that applies the last two function arguments
||| to the given function value.
export
appConvs : {is : Types} -> Val (a -> b -> c) -> Conversions (is:<a:<b) (is:<c)
appConvs x =
  weakenConvs (weakenConvs fromTypes) :<
    CApp (CApp (CPure x) (CAt $ Pre Lst)) (CAt Lst)

||| Appends a argument to the list of inputs and outputs.
export
appendConv : Conversions is os -> Conversions (is:<t) (os:<t)
appendConv sc = weakenConvs sc :< CAt Lst

||| Flips the last two input arguments in the output.
export
flipConv : Conversions is (os:<a:<s) -> Conversions is (os:<s:<a)
flipConv (sc:<x:<y) = sc:<y:<x

||| Drops the last argument
export
drop : {is : Types} -> Conversions (is:<c) is
drop = let (i:<_) := fromTypes {is = is:<c} in i

||| Drops the last argument
export
appendChar : {is : Types} -> Conversions is (is:<Char)
appendChar = fromTypes :< CPure charVal

export
flipLast : {is : Types} -> Conversions (is:<a:<s) (is:<s:<a)
flipLast = flipConv fromTypes

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

export
convToVal : UConversion -> Value
convToVal (UAt k)     = VPlain "x\{show k}"
convToVal (UApp x y)  = VApp (convToVal x) (convToVal y)
convToVal (UPure x y) = y

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

export
uconvs : Conversions is os -> UConversions
uconvs [<]      = [<]
uconvs (x :< c) = uconvs x :< uconv c

namespace UConversions
  export
  fromTypes : Nat -> Types -> UConversions
  fromTypes _ [<]     = [<]
  fromTypes n (si:<i) = fromTypes (S n) si :< UAt n

  export
  appendChar : Types -> UConversions
  appendChar ts = fromTypes 0 ts :< uconv {is = [<]} (CPure charVal)

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

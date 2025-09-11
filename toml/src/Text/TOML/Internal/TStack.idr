module Text.TOML.Internal.TStack

import public Data.Time.Time
import public Data.SortedMap
import Derive.Prelude
import Text.ILex.Bounds
import Text.ILex.Error

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Floating Point Literals
--------------------------------------------------------------------------------

public export
data TomlFloat : Type where
  NaN   : TomlFloat
  Infty : Sign -> TomlFloat
  Float : Double -> TomlFloat

%runElab derive "TomlFloat" [Eq,Show]

export
Interpolation TomlFloat where
  interpolate NaN         = "nan"
  interpolate (Infty x)   = "\{x}inf"
  interpolate (Float dbl) = show dbl

--------------------------------------------------------------------------------
--          TomlValue and Table
--------------------------------------------------------------------------------

||| Data type for trees of TOML data.
public export
data TomlValue : Type where
  ||| A string literal
  TStr  : String -> TomlValue

  ||| A boolean literal
  TBool : Bool -> TomlValue

  ||| A date-time literal
  TTime : AnyTime -> TomlValue

  ||| An integer
  TInt  : Integer -> TomlValue

  ||| A floating point number
  TDbl  : TomlFloat  -> TomlValue

  ||| An array of values
  TArr  : SnocList TomlValue -> TomlValue

  ||| A table of key-value pairs
  TTbl  : SortedMap String TomlValue -> TomlValue

%name TomlValue v,v1,v2
%runElab derive "TomlValue" [Eq,Show]

||| Currently, a TOML table is a list of pairs. This might be later
||| changed to some kind of dictionary.
public export
0 TomlTable : Type
TomlTable = SortedMap String TomlValue

%name TomlTable t,t1,t2

--------------------------------------------------------------------------------
--          Keys
--------------------------------------------------------------------------------

public export
data KeyType = Plain | Quoted | Literal

%runElab derive "KeyType" [Eq,Show]

public export
record Key where
  constructor KT
  key    : String
  tpe    : KeyType
  bounds : Bounds

%name Key k,k2,k3
%runElab derive "Key" [Eq,Show]

export
Interpolation Key where
  interpolate (KT k t _) = case t of
    Plain   => k
    Quoted  => show k
    Literal => "'\{k}'"

Interpolation (List Key) where
  interpolate = fastConcat . intersperse "." . map interpolate

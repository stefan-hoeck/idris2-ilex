module Text.TOML.Types

import public Data.Time.Time
import public Data.SortedMap
import Derive.Prelude
import Text.Bounds
import Text.ParseError

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
  interpolate NaN          = "nan"
  interpolate (Infty Plus) = "inf"
  interpolate (Infty _)    = "-inf"
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
  TArr  : List TomlValue -> TomlValue

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

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

public export
data TomlParseError : Type where
  ValueExists       : List Key -> TomlParseError
  InlineTableExists : List Key -> TomlParseError
  TableExists       : List Key -> TomlParseError
  StaticArray       : List Key -> TomlParseError
  TableArray        : List Key -> TomlParseError
  InvalidLeapDay    : LocalDate -> TomlParseError

%runElab derive "TomlParseError" [Eq,Show]

export
Interpolation TomlParseError where
  interpolate (ValueExists k) =
    "Trying to overwrite an existing value: \{k}"
  interpolate (InlineTableExists k) =
    "Trying to overwrite an existing inline table: \{k}"
  interpolate (TableExists k) =
    "Trying to overwrite an existing table: \{k}"
  interpolate (StaticArray k) =
    "Trying to overwrite an existing array: \{k}"
  interpolate (TableArray k) =
    "Trying to overwrite an existing array of tables: \{k}"
  interpolate (InvalidLeapDay d) = "Invalid leap day: \{d}"

||| Error type when lexing and parsing TOML files
public export
0 TErr : Type
TErr = BoundedErr TomlParseError

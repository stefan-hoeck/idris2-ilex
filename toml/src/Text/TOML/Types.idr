module Text.TOML.Types

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
--          Table Type
--------------------------------------------------------------------------------

public export
data TableType = Inline | Table

%runElab derive "TableType" [Show,Eq,Ord]

public export
data ArrayType = Static | OfTables

%runElab derive "ArrayType" [Show,Eq,Ord]

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
  TArr  : ArrayType -> SnocList TomlValue -> TomlValue

  ||| A table of key-value pairs
  TTbl  : TableType -> SortedMap String TomlValue -> TomlValue

%runElab derive "TomlValue" [Eq,Show]

||| Currently, a TOML table is a list of pairs. This might be later
||| changed to some kind of dictionary.
public export
0 TomlTable : Type
TomlTable = SortedMap String TomlValue

--------------------------------------------------------------------------------
--          Tokens
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

%runElab derive "TomlParseError" [Eq,Show]

export
Interpolation TomlParseError where
  interpolate (ValueExists k) =
    "Trying to overwrite existing value: \{k}"
  interpolate (InlineTableExists k) =
    "Trying to modify existing inline table: \{k}"
  interpolate (TableExists k) =
    "Trying to overwrite existing table: \{k}"
  interpolate (StaticArray k) =
    "Trying to modify a static array: \{k}"

||| Error type when lexing and parsing TOML files
public export
0 TErr : Type
TErr = BoundedErr TomlParseError

--------------------------------------------------------------------------------
--          Table Lookup
--------------------------------------------------------------------------------

public export
data Path : Type where
  Root : Path
  Tbl  : (p : Path) -> (t : TomlTable) -> (k : Key) -> Path
  New  : (p : Path) -> (k : Key) -> Path
  Arr  : (p : Path) -> (sv : SnocList TomlValue) -> Path

export
unwind : TomlValue -> Path -> TomlTable

unwindTbl : TomlTable -> Path -> TomlTable
unwindTbl t Root        = t
unwindTbl t (Tbl p x k) = unwindTbl (insert k.key (TTbl Table t) x) p
unwindTbl t (New p k)   = unwindTbl (insert k.key (TTbl Table t) empty) p
unwindTbl t (Arr p sv)  = unwind (TArr OfTables (sv:<TTbl Table t)) p

unwind v (Tbl p t k) = unwindTbl (insert k.key v t) p
unwind v (New p k)   = unwindTbl (insert k.key v empty) p
unwind v (Arr p sv)  = unwind (TArr OfTables (sv:<v)) p
unwind v Root        = empty

keys : List Key -> Path -> List Key
keys ks Root        = ks
keys ks (Tbl p t k) = keys (k::ks) p
keys ks (New p k)   = keys (k::ks) p
keys ks (Arr p sv)  = keys ks p

exists : Path -> TomlValue -> Either TErr a
exists p v =
 let ks := keys [] p
     bs := foldMap bounds ks
  in case v of
       TArr Static sx => custom bs $ StaticArray ks
       TTbl Inline y  => custom bs $ InlineTableExists ks
       TTbl Table y   => custom bs $ TableExists ks
       _              => custom bs $ ValueExists ks

emptyPath : Path -> List Key -> Path
emptyPath p []        = p
emptyPath p (k :: ks) = emptyPath (New p k) ks

export
valuePath : Path -> List Key -> TomlTable -> Either TErr Path
valuePath p []        t = exists p (TTbl Table t)
valuePath p (k :: ks) t =
  case lookup k.key t of
    Nothing              => Right $ emptyPath (Tbl p t k) ks
    Just (TTbl Table t2) => valuePath (Tbl p t k) ks t2
    Just v               => exists p v

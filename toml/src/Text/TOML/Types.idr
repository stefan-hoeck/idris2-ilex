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
--          TomlValue and Table
--------------------------------------------------------------------------------

public export
data TableType = Inline | Table | Def

%runElab derive "TableType" [Show,Eq,Ord]

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

  ||| An array of tables
  TTbls : SnocList (SortedMap String TomlValue) -> TomlValue

  ||| A table of key-value pairs
  TTbl  : TableType -> SortedMap String TomlValue -> TomlValue

%name TomlValue v,v1,v2
%runElab derive "TomlValue" [Eq,Show]

||| Currently, a TOML table is a list of pairs. This might be later
||| changed to some kind of dictionary.
public export
0 TomlTable : Type
TomlTable = SortedMap String TomlValue

%name TomlTable t,t1,t2

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
  interpolate (TableArray k) =
    "Trying to overwrite an array of tables: \{k}"

||| Error type when lexing and parsing TOML files
public export
0 TErr : Type
TErr = BoundedErr TomlParseError

--------------------------------------------------------------------------------
--          Table Lookup
--------------------------------------------------------------------------------

public export
data TView : Type where
  Root : TView
  Tbl  : TView -> TomlTable -> Key -> TView
  New  : TView -> TomlTable -> Key -> TView
  Arr  : TView -> TomlTable -> Key -> SnocList TomlTable -> TomlTable -> TView

compatible : TableType -> TableType -> Bool
compatible Inline Inline = True
compatible Inline _      = False
compatible _      Inline = False
compatible _      _      = True

export
reduceT : TableType -> TomlTable -> TView -> TomlTable
reduceT tt t1 Root              = t1
reduceT tt t1 (Tbl v t2 k)      = reduceT tt (insert k.key (TTbl tt t1) t2) v
reduceT tt t1 (New v t2 k)      = reduceT tt (insert k.key (TTbl tt t1) t2) v
reduceT tt t1 (Arr v t2 k st _) = reduceT tt (insert k.key (TTbls (st:<t1)) t2) v

keys : List Key -> TView -> List Key
keys ks Root            = ks
keys ks (Tbl v _ k)     = keys (k::ks) v
keys ks (New v _ k)     = keys (k::ks) v
keys ks (Arr v _ k _ _) = keys (k::ks) v

export
exists : List Key -> TView -> TomlValue -> TErr
exists add view val =
 let ks := keys add view
     bs := foldMap bounds ks
  in case val of
       TArr _        => B (Custom $ StaticArray ks) bs
       TTbls {}      => B (Custom $ TableArray ks) bs
       TTbl Inline _ => B (Custom $ InlineTableExists ks) bs
       TTbl Table _  => B (Custom $ TableExists ks) bs
       _             => B (Custom $ ValueExists ks) bs

new : TView -> List Key -> TView
new v []        = v
new v (k :: ks) = new (New v empty k) ks

export
view : TableType -> TView -> TomlTable -> List Key -> Either TErr TView
view _  v t []      = Right v
view tt v t (k::ks) =
  case lookup k.key t of
    Nothing               => Right $ new (New v t k) ks
    Just (TTbls $ st:<t2) => view tt (Arr v t k st t2) t2 ks
    Just x@(TTbl tt2 t2) => case compatible tt tt2 of
      True  => view tt (Tbl v t k) t2 ks
      False => Left $ exists [k] v x
    Just val              => Left $ exists [k] v val

public export
data TStack : Type where
  STbl : TomlTable -> SnocList Key -> TStack
  SArr : TomlTable -> SnocList Key -> TStack
  STop : TView -> SnocList Key -> TomlTable -> TStack
  VArr : TStack -> SnocList TomlValue -> TStack
  VTbl : TStack -> SnocList Key -> TomlTable -> TStack

export
toRoot : TStack -> TomlTable
toRoot (STbl t sk)   = t
toRoot (SArr t sk)   = t
toRoot (STop v sk t) = reduceT Table t v
toRoot (VArr x sv)   = toRoot x
toRoot (VTbl x sk y) = toRoot x

export
empty : TStack
empty = STop Root [<] empty

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

  ||| An array of tables
  TTbls : SnocList (SortedMap String TomlValue) -> TomlValue

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

%name TomlTable t,t1,t2

public export
data View : Type where
  Root : View
  Tbl  : View -> TomlTable -> Key -> View
  Arr  : View -> SnocList TomlTable -> View

keys : List Key -> View -> List Key
keys ks Root        = ks
keys ks (Tbl v _ k) = keys (k::ks) v
keys ks (Arr v _)   = keys ks v

exists : List Key -> View -> TomlValue -> Either TErr a
exists add view val =
 let ks := keys add view
     bs := foldMap bounds ks
  in case val of
       TArr sx       => custom bs $ StaticArray ks
       TTbl Inline y => custom bs $ InlineTableExists ks
       TTbl Table y  => custom bs $ TableExists ks
       _             => custom bs $ ValueExists ks

vexists : View -> Either TErr a

new : View -> List Key -> (View,Bool,TomlTable)
new v []        = (v,True,empty)
new v (k :: ks) = new (Tbl v empty k) ks

view : Bool -> View -> TomlTable -> List Key -> Either TErr (View,Bool,TomlTable)
view inline v t []      = Right (v,False,t)
view inline v t (k::ks) =
  case lookup k.key t of
    Nothing               => Right $ new (Tbl v t k) ks
    Just (TTbls $ st:<t2) => view inline (Arr (Tbl v t k) st) t2 ks
    Just x@(TTbl tt t2) => case (tt,inline) of
      (Table,False) => view inline (Tbl v t k) t2 ks
      (Inline,True) => view inline (Tbl v t k) t2 ks
      _             => exists [k] v x
    Just val              => exists [k] v val

public export
data Stck : Type where
  STbl : TomlTable -> SnocList Key -> Stck
  SArr : TomlTable -> SnocList Key -> Stck
  STop : View -> TomlTable -> SnocList Key -> Stck
  VArr : Stck -> SnocList TomlValue -> Stck
  VTbl : Stck -> TomlTable -> SnocList Key -> Stck

close : Stck -> Either TErr Stck
close (STbl t sk) =
  case view False Root t (sk <>> []) of
    Right (v@(Tbl {}), True, t) => Right (STop v t [<])
    Right (v,_)                 => vexists v
    Left  x                     => Left x
close (SArr t sk) =
  case view False Root t (sk <>> []) of
    Right (v@(Tbl {}), True, t) => Right (STop (SArr v [<empty]) [<])
    Right (v,_)                 => vexists v
    Left  x                     => Left x
close (STop x y sk) = ?fooo_2
close (VArr x sx)   = ?fooo_3
close (VTbl x y sk) = ?fooo_4

export
init : Stck

module Text.TOML.Internal.TStack

import Data.Time.Time
import Data.SortedMap
import Derive.Prelude
import Text.ILex
import Text.TOML.Lexer
import Text.TOML.Types
import Syntax.T1

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Tree and Tables
--------------------------------------------------------------------------------

public export
data Tag = New | Undef | Def

%runElab derive "Tag" [Eq,Show,Ord]

public export
data Tree : Type where
  TV : TomlValue -> Tree
  TT : Tag -> SortedMap String Tree -> Tree
  TA : SnocList (SortedMap String Tree) -> SortedMap String Tree -> Tree

public export
0 TreeTable : Type
TreeTable = SortedMap String Tree

toVal : Tree -> TomlValue

toArr : List TomlValue -> SnocList TreeTable -> TomlValue

export
toTbl : TreeTable -> TomlTable
toTbl t = assert_total $ map toVal t

toVal (TV v)    = v
toVal (TT x t)  = TTbl (toTbl t)
toVal (TA sx x) = toArr [TTbl $ toTbl x] sx

toArr vs [<]     = TArr vs
toArr vs (st:<t) = toArr (TTbl (toTbl t) :: vs) st

public export
data TView : Type -> Type where
  VR : TView t
  VT : TView t -> SortedMap String t -> Key -> Tag -> TView t
  VA : TView Tree -> TreeTable -> Key -> SnocList TreeTable -> TView Tree

keys : List Key -> TView t -> List Key
keys ks VR           = ks
keys ks (VT v _ k _) = keys (k::ks) v
keys ks (VA v _ k _) = keys (k::ks) v

export
exists : List Key -> TView t -> TomlValue -> TErr
exists add view val =
 let ks := keys add view
     bs := foldMap bounds ks
  in case val of
       TArr _ => B (Custom $ StaticArray ks) bs
       TTbl _ => B (Custom $ TableExists ks) bs
       _      => B (Custom $ ValueExists ks) bs

export
vexists : TView t -> TErr
vexists (VA v _ k _) = exists [k] v (TArr [])
vexists v            = exists [] v (TTbl empty)

new : TView t -> List Key -> TView t
new v []        = v
new v (k :: ks) = new (VT v empty k New) ks

export
view : TView Tree -> TreeTable -> List Key -> Either TErr (TView Tree,TreeTable)
view v t []      = Right (v,t)
view v t (k::ks) =
  case lookup k.key t of
    Nothing         => Right (new (VT v t k New) ks, empty)
    Just (TT tt t2) => view (VT v t k tt) t2 ks
    Just (TA st t2) => view (VA v t k st) t2 ks
    Just (TV val)   => Left $ exists [k] v val

export
tview : TreeTable -> List Key -> Either TErr (TView Tree,TreeTable)
tview t ks =
  case view VR t ks of
    Right (v@(VT _ _ _ Def),_) => Left $ exists [] v (TTbl empty)
    Right (v@(VA {}),_)        => Left $ exists [] v (TArr [])
    res                        => res

export
iview : TView TomlValue -> TomlTable -> List Key -> Either TErr (TView TomlValue)
iview v t []      = Right v
iview v t (k::ks) =
  case lookup k.key t of
    Nothing        => Right $ new (VT v t k New) ks
    Just (TTbl t2) => iview (VT v t k Def) t2 ks
    Just val       => Left $ exists [k] v val

export
reduceT : Tag -> TreeTable -> TView Tree -> TreeTable
reduceT x t VR             = t
reduceT x t (VT v t2 k y)  = reduceT x (insert k.key (TT (max x y) t) t2) v
reduceT x t (VA v t2 k st) = reduceT x (insert k.key (TA st t) t2) v

export
reduceI : TomlTable -> TView TomlValue -> TomlTable
reduceI t VR            = t
reduceI t (VT v t2 k _) = reduceI (insert k.key (TTbl t) t2) v

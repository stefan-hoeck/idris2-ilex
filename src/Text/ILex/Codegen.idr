module Text.ILex.Codegen

import Control.Monad.State
import Data.Nat
import Data.SortedMap
import Data.String

import Text.PrettyPrint.Bernardy

import Text.ILex.Char.UTF8
import Text.ILex.Internal.DFA
import Text.ILex.Internal.Types

import public Data.List
import public Text.ILex.RExp

%default total

export covering
gencode :
     {auto tt  : ToType a}
  -> (name     : String)
  -> (tm       : TokenMap (Val $ Conv a))
  -> {auto 0 p : NonEmpty tm}
  -> List String

--------------------------------------------------------------------------------
-- Implementation
--------------------------------------------------------------------------------

pair : (Nat, Val $ Conv a) -> String
pair (n,v) = "(\{show n}, \{v.val})"

terminals : ToType a => Nat -> List (Nat, Val $ Conv a) -> List String
terminals size ps =
  let infTpe := App "Maybe" (App "Info" $ tpeof a)
      arrTpe := App (App "IArray" $ Plain (show size)) infTpe
   in case ps of
        []   => ["terms : \{arrTpe}", "terms = fill _ Nothing"]
        h::t =>
             "terms : \{arrTpe}"
          :: "terms ="
          :: "  fromPairs \{show size} Nothing"
          :: "    [ \{pair h}"
          :: map (\p => "    , \{pair p}") t
          ++ ["    ]"]

node : Nat -> Node -> String
node n (N _ acc out) = "fromIPairs \{show n} " ++ show (out >>= transitions)

term : SortedMap Nat (Val $ Conv a) -> Node -> Maybe (Nat,Val $ Conv a)
term m (N _ []     _) = Nothing
term m (N n (t::_) _) = (n,) <$> lookup t m

states : List Node -> List String
states []      = []
states (n::ns) =
  let len  := length ns
      lens := show (S len)
   in    "states : IArray \{lens} (IArray 256 (Fin \{lens}))"
      :: "states ="
      :: "  array"
      :: "    [ \{node len n}"
      :: map (\n => "    , \{node len n}") ns
      ++ ["    ]"]

gencode name tm =
  let M tms graph := machine (toDFA tm toByteRanges)
      nodes       := values graph
      len         := length nodes
      terms       := terminals len (mapMaybe (term tms) nodes)
      sts         := states nodes
      lexTpe      := App "Lexer" (tpeof a)
   in    "export"
      :: "\{name} : \{lexTpe}"
      :: "\{name} = L \{show $ pred len} states terms"
      :: "  where"
      :: map (String.indent 4) (terms ++ (""::sts))

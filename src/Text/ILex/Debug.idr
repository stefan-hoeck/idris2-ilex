module Text.ILex.Debug

import Control.Monad.State
import Data.ByteString
import Data.Linear.Traverse1
import Data.SortedMap
import Data.String
import Derive.Pretty
import Language.Reflection.Pretty

import Text.ILex.Char.UTF8
import Text.ILex.Internal.DFA
import Text.ILex.Internal.ENFA
import Text.ILex.Internal.NFA
import Text.ILex.Internal.Types
import Text.ILex.Lexer
import Text.ILex.RExp

%default total

export
appLst : {d : _} -> Doc d -> List (Doc d) -> Doc d
appLst nm [] = nm
appLst nm ds = nm `vappend` (indent 2 $ vsep ds)

export
strLst : {d : _} -> String -> List (Doc d) -> Doc d
strLst = appLst . line

export
prettyNats : {d : _} -> List Nat -> Doc d
prettyNats []      = line ""
prettyNats [n]     = line (show n)
prettyNats (n::ns) = line (show n) <+> comma <+> prettyNats ns

export
Pretty Range8 where
  prettyPrec p r =
    let l := lowerBound r
        u := upperBound r

     in if l > u then line "<empty>"
        else if l == u then line (show l)
        else line "\{show l}-\{show u}"

export
prettyEdge : {d : _} -> Edge -> Doc d
prettyEdge (E r tgt) = pretty r <+> colon <++> line (show tgt)

export
prettyENode : {d : _} -> (Nat,ENode) -> Doc d
prettyENode (n, EN accs eps ds) =
  appLst (line "Node" <++> pretty n)
    [ line   "acc:      " <+> prettyNats accs
    , line   "eps:      " <+> prettyNats eps
    , strLst "deltas:   " (map prettyEdge ds)
    ]

export
prettyNEdge : {d : _} -> NEdge -> Doc d
prettyNEdge (NE r tgts) = pretty r <+> colon <++> line (show tgts)

export
prettyNNode : {d : _} -> (Nat,NNode) -> Doc d
prettyNNode (n, NN _ accs ds) =
  appLst (line "Node" <++> pretty n)
    [ line   "acc:      " <+> prettyNats accs
    , strLst "deltas:   " (map prettyNEdge ds)
    ]

export
prettyNode : {d : _} -> (Nat,Node) -> Doc d
prettyNode (n, N _ acc ds) =
  appLst (line "Node" <++> pretty n)
    [ line   "acc:      " <+> prettyNats acc
    , strLst "deltas:   " (map prettyEdge ds)
    ]

export
Pretty EGraph where
  prettyPrec p g =
    strLst "graph:" (map prettyENode $ SortedMap.toList g)

export
Pretty NGraph where
  prettyPrec p g =
    strLst "graph:" (map prettyNNode $ SortedMap.toList g)

export
Pretty Graph where
  prettyPrec p g =
    strLst "graph:" (map prettyNode $ SortedMap.toList g)

terminal : Pretty a => {d : _} -> (Nat, a) -> Doc d
terminal (n,c) = line (show n) <+> colon <++> pretty c

export
Pretty a => Pretty b => Pretty (Machine a b) where
  prettyPrec p (M sm g) =
    vsep
      [ appLst (line "Terminals") (map terminal $ SortedMap.toList sm)
      , pretty g
      ]

export covering
prettyENFA : Pretty a => TokenMap8 a -> IO ()
prettyENFA tm = putPretty $ machine $ toENFA tm

export covering
prettyNFA : Pretty a => TokenMap8 a -> IO ()
prettyNFA tm = putPretty $ machine $ toNFA tm

export covering
prettyDFA : Pretty a => TokenMap8 a -> IO ()
prettyDFA tm = putPretty $ machine $ toDFA tm

--------------------------------------------------------------------------------
-- Lexer Pretty Printing
--------------------------------------------------------------------------------

prettyByte : {d : _} -> Nat -> Doc d
prettyByte n = line "\{pre} \{toHex $ cast n}"
  where
    pre : String
    pre =
     case n >= 128 || Prelude.isControl (cast n) of
       True  => "   "
       False => "'\{String.singleton $ cast n}'"

prettyTok : Pretty a => {d : _} -> Tok e a -> Doc d
prettyTok Ignore    = line "<ignore>"
prettyTok (Const x) = pretty x
prettyTok (Parse f) = line "<parse>"

prettyByteStep : Pretty a => {d : _} -> (Nat, ByteStep n e a) -> Doc d
prettyByteStep (x,bs) =
  vsep
    [ line (show x)
    , indent 2 $ vsep (mapMaybe trans $ zipWithIndex $ toList bs)
    ]

  where
    trans : (Nat, Transition n e a) -> Maybe (Doc d)
    trans (byte,t) =
      case t of
        KeepT y   => Just (prettyByte byte <+> colon <++> prettyTok y <++> line "(stay)")
        Done y    => Just (prettyByte byte <+> colon <++> prettyTok y <++> line "(done)")
        Keep      => Just (prettyByte byte <+> colon <++> line "stay")
        Move y    => Just (prettyByte byte <+> colon <++> line "-> \{show y}")
        MoveT y z => Just (prettyByte byte <+> colon <++> prettyTok z <++> line "(-> \{show y})")
        Bottom    => Nothing

export
Pretty a => Pretty (DFA e a) where
  prettyPrec p (L _ next) =
    vsep $ prettyByteStep <$> zipWithIndex (toList next)

export
prettyLexer : Pretty a => DFA e a -> IO ()
prettyLexer dfa = putPretty dfa

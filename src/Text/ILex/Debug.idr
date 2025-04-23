module Text.ILex.Debug

import Control.Monad.State
import Data.SortedMap
import Data.ByteString
import Data.String
import Derive.Pretty
import Language.Reflection.Pretty

import Text.ILex.Char.UTF8
import Text.ILex.RExp
import Text.ILex.Internal.DFA
import Text.ILex.Internal.ENFA
import Text.ILex.Internal.NFA
import Text.ILex.Internal.Types

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
Pretty (Conv a) where
  prettyPrec p Ignore     = line "Ignore"
  prettyPrec p (Const v1) = line "Const" <+> colon <+> pretty v1
  prettyPrec p (Txt v1)   = line "Txt"   <+> colon <+> pretty v1
  prettyPrec p (Chr v1)   = line "Chr"   <+> colon <+> pretty v1
  prettyPrec p (Len v1)   = line "Len"   <+> colon <+> pretty v1

export
Pretty (Acc a) where
  prettyPrec p (A tgt c) = line (show tgt) <+> colon <+> pretty c

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
prettyENode : {d : _} -> (Nat,ENode a) -> Doc d
prettyENode (n, EN accs eps ds) =
  appLst (line "Node" <++> pretty n)
    [ line   "acc:      " <+> prettyNats (map tgt accs)
    , line   "eps:      " <+> prettyNats eps
    , strLst "deltas:   " (map prettyEdge ds)
    ]

export
prettyNEdge : {d : _} -> NEdge -> Doc d
prettyNEdge (NE r tgts) = pretty r <+> colon <++> line (show tgts)

export
prettyNNode : {d : _} -> (Nat,NNode a) -> Doc d
prettyNNode (n, NN _ accs ds) =
  appLst (line "Node" <++> pretty n)
    [ line   "acc:      " <+> prettyNats (map tgt accs)
    , strLst "deltas:   " (map prettyNEdge ds)
    ]

export
prettyNode : {d : _} -> (Nat,Node a) -> Doc d
prettyNode (n, N _ acc ds) =
  appLst (line "Node" <++> pretty n)
    [ line   "acc:      " <+> prettyNats (map tgt acc)
    , strLst "deltas:   " (map prettyEdge ds)
    ]

export
Pretty (EGraph a) where
  prettyPrec p g =
    strLst "graph:" (map prettyENode $ SortedMap.toList g)

export
Pretty (NGraph a) where
  prettyPrec p g =
    strLst "graph:" (map prettyNNode $ SortedMap.toList g)

export
Pretty (Graph a) where
  prettyPrec p g =
    strLst "graph:" (map prettyNode $ SortedMap.toList g)

export covering
prettyENFA : TokenMap a -> IO ()
prettyENFA tm = putPretty $ evalNorm $ toENFA tm toByteRanges

export covering
prettyNFA : TokenMap a -> IO ()
prettyNFA tm = putPretty $ evalNorm $ toNFA tm toByteRanges

export covering
prettyDFA : TokenMap a -> IO ()
prettyDFA tm = putPretty $ evalNorm $ toDFA tm toByteRanges

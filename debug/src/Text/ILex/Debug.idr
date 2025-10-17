module Text.ILex.Debug

import Control.Monad.State
import Data.ByteString
import Data.Linear.Traverse1
import Data.SortedMap
import Data.String
import Derive.Pretty
import Language.Reflection.Pretty

import Text.ILex.Char.UTF8
import Text.ILex.Stack
import Text.ILex.Internal.DFA
import Text.ILex.Internal.ENFA
import Text.ILex.Internal.NFA
import Text.ILex.Internal.Types
import Text.ILex.Parser
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
Pretty (List (Nat,ENode)) where
  prettyPrec p g = strLst "graph:" (map prettyENode g)

export
Pretty (List (Nat,NNode)) where
  prettyPrec p g = strLst "graph:" (map prettyNNode g)

export
Pretty (List (Nat,Node)) where
  prettyPrec p g = strLst "graph:" (map prettyNode g)

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
prettyByte n = line "\{pre} 0x\{toHex $ cast n}"
  where
    pre : String
    pre =
     case n >= 128 || Prelude.isControl (cast n) of
       True  => "   "
       False => "'\{String.singleton $ cast n}'"

export
Pretty a => Pretty (Tok e a) where
  prettyPrec _ Ignore    = line "<ignore>"
  prettyPrec _ (Const x) = pretty x
  prettyPrec _ (Txt   f) = line "<Txt>"
  prettyPrec _ (Bytes f) = line "<Bytes>"

prettyByteStep : {d : _} -> (Nat, ByteStep n q r s) -> Doc d
prettyByteStep (x,bs) =
  vsep
    [ line (show x)
    , indent 2 $ vsep (mapMaybe trans $ zipWithIndex $ toList bs)
    ]

  where
    trans : (Nat, Transition n q r s) -> Maybe (Doc d)
    trans (byte,t) =
      case t of
        Keep       => Just (prettyByte byte <+> colon <++> line "stay")
        Done y     => Just (prettyByte byte <+> colon <++> line "done")
        DoneBS y   => Just (prettyByte byte <+> colon <++> line "done with bytes")
        Move y z   => Just (prettyByte byte <+> colon <++> line "move (\{show y})")
        MoveE y    => Just (prettyByte byte <+> colon <++> line "move non-terminal (\{show y})")
        Bottom     => Nothing

export
Pretty (DFA q r s) where
  prettyPrec p (L _ next) =
    vsep $ prettyByteStep <$> zipWithIndex (toList next)

export
prettyLexer : DFA q r s -> IO ()
prettyLexer dfa = putPretty dfa

export
prettyParser :
     {r : _}
  -> {default False details : Bool}
  -> (Index r -> String)
  -> P1 World e r s a
  -> IO ()
prettyParser shw p = go 0 0
  where
    go : Nat -> Bits32 -> IO ()
    go tot v =
      case lt v r of
        Just0 prf =>
          let lx := p.lex `at` I v
           in case details of
                False => Prelude.do
                  putStrLn "\{shw $ I v} (\{show $ S lx.states} states)"
                  go (tot + lx.states) (assert_smaller v $ v+1)
                True  => Prelude.do
                  putStrLn "\{shw $ I v} (\{show $ S lx.states} states): "
                  prettyLexer lx
                  putStrLn ""
                  go (tot + lx.states) (assert_smaller v $ v+1)
        Nothing0  => putStrLn "Total: \{show tot} state transitions"

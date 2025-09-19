module Text.ILex.Internal.ENFA

import Data.Array.Core
import Data.Array.Mutable
import Data.Linear.Traverse1
import Syntax.T1
import Text.ILex.Internal.Types
import Text.ILex.RExp

%default total

--------------------------------------------------------------------------------
-- Conversion to ENFA
--------------------------------------------------------------------------------

parameters {auto st : DFAState s a}
  enfa : RExp8 b -> (tgt : Nat) -> F1 s Nat
  enfa Eps       tgt = pure tgt
  enfa (And x y) tgt = enfa y tgt >>= enfa x
  enfa (Ch x)    tgt = createENode (EN [] [] $ map (`E` tgt) $ ranges x)
  enfa (Or x y)  tgt = T1.do
    tx <- enfa x tgt
    ty <- enfa y tgt
    createENode (EN [] [tx,ty] [])

  enfa (Star x)  tgt = do
    me <- inc
    tx <- enfa x me
    insertENode me (EN [] [tx,tgt] [])

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

  ||| Compiles an expression to a graph with epsilon transitions
  export
  toENFA : TokenMap8 a -> F1' s
  toENFA rs = T1.do
    ps <- traverse1 (\x => (,x) <$> inc) rs
    traverse1_ insertTerminal ps
    ts <- traverse1 (\(n,r,c) => enfa r n) ps
    ignore1 $ insertENode 0 (EN [] ts [])

  export %inline
  debugENFA : TokenMap8 a -> F1 s (List (Nat, ENode))
  debugENFA ts = toENFA ts >> pairs1 st.egraph

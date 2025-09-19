module Text.ILex.Internal.DFA

import Data.Linear.Traverse1
import Syntax.T1
import Text.ILex.Internal.ENFA
import Text.ILex.Internal.NFA
import Text.ILex.Internal.Types

%default total

parameters {auto st : DFAState s a}

  covering
  process : SnocList Edge -> NEdges -> F1 s Edges

  covering
  discrete : Nat -> F1' s
  discrete x = T1.do
    Nothing <- lookupNode x | Just v => pure ()
    nn      <- getNNode x
    ds      <- process [<] nn.out
    let nde := N nn.pos nn.acc ds
    insertNode x nde

  process sx []              = pure (sx <>> [])
  process sx (NE r ts :: xs) = T1.do
    case ts of
      -- oops, there is no possible target for this rule. we can drop it
      []  => process sx xs

      -- a single target so this rule is already discrete
      -- let's keep it and move on
      [t] => process (sx:<E r t) xs

      -- a group of targets. let's see if we already have seen these
      set =>
        lookupSet set >>= \case
          -- this is a known group.
          Just t  => process (sx:<E r t) xs

          -- a new group. we have work to do
          Nothing => do
            t  <- addSet set
            ns <- traverse1 getNNode set
            insertNNode t (foldl joinNNode (NN t [] []) ns)
            discrete t
            process (sx:<E r t) xs

  covering
  nodes : F1' s
  nodes = keys1 st.ngraph >>= traverse1_ discrete

  export covering
  toDFA : TokenMap8 a -> F1 s (List (Nat,Node))
  toDFA xs = T1.do
    toNFA xs
    nodes
    connectedComponent children 0 st.graph
    normalizeGraph
    pairs1 st.graph

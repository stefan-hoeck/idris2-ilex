module Text.ILex.Internal.NFA

import Data.Linear.Traverse1
import Data.Maybe
import Syntax.T1
import Text.ILex.Internal.ENFA
import Text.ILex.Internal.Types

%default total

prep : NEdge -> NEdges -> NEdges
prep x xs = if isEmpty x.rule then xs else x::xs

split : NEdge -> NEdge -> (NEdge,NEdge,NEdge)
split x y =
  let ri := intersection x.rule y.rule
      ei := NE ri (sunion x.tgts y.tgts)
      Left rx := difference x.rule ri
        | Right (a,b) => (NE a x.tgts,ei,NE b x.tgts)
      Left ry := difference y.rule ri
        | Right (a,b) => (NE a y.tgts,ei,NE b y.tgts)
   in case rx < ry of
        True  => (NE rx x.tgts,ei,NE ry y.tgts)
        False => (NE ry y.tgts,ei,NE rx x.tgts)

insertEdge : NEdges -> NEdge -> NEdges
insertEdge []           x     = if isEmpty x.rule then [] else [x]
insertEdge es@(y :: ys) x     =
  case isEmpty x.rule of
    True  => es
    False => case x.tgts == y.tgts of
      False => case overlap x.rule y.rule of
        False => case x.rule < y.rule of
          True  => prep x es
          False => y :: insertEdge ys x
        True  =>
          let (ex,ei,ey) := split x y
           in prep ex . prep ei $ insertEdge ys ey

      -- They share the same targets. We try and build one large range
      -- from the two.
      True  => case overlap x.rule y.rule || adjacent x.rule y.rule of
        False => case x.rule < y.rule of
          True  => prep x es
          False => y :: insertEdge ys x
        True  => NE (span x.rule y.rule) x.tgts :: ys

outUnion : NEdges -> NEdges -> NEdges
outUnion xs ys = foldl insertEdge ys xs

export
joinNNode : NNode -> NNode -> NNode
joinNNode x y = NN x.pos (sunion x.acc y.acc) (outUnion x.out y.out)

fromEdge : Edge -> NEdge
fromEdge (E r t) = (NE r [t])

fromENode : Nat -> ENode -> NNode
fromENode n x = NN n x.acc $ map fromEdge x.out

parameters {auto st : DFAState s a}
  covering
  eclosure : Nat -> F1 s NNode
  eclosure x = T1.do
    Nothing <- lookupNNode x | Just v => pure v
    n       <- getENode x
    es      <- traverse1 eclosure n.eps
    let nn := foldl joinNNode (fromENode x n) es
    insertNNode x nn
    pure nn

  covering
  closures : F1' s
  closures = keys1 st.egraph >>= traverse1_  (ignore1 . eclosure)

  export covering
  toNFA : TokenMap8 a -> F1' s
  toNFA xs = T1.do
    toENFA xs
    closures
    connectedComponent nchildren 0 st.ngraph

  export %inline
  debugNFA : TokenMap8 a -> F1 s (List (Nat, NNode))
  debugNFA ts = assert_total (toNFA ts) >> pairs1 st.ngraph

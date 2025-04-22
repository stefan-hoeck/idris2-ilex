module Text.ILex.Internal.NFA

import Control.Monad.State
import Data.Maybe
import Data.SortedMap
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
insertEdge []           x     = [x]
insertEdge es@(y :: ys) x     =
  case x.tgts == y.tgts of
    False => case overlap x.rule y.rule of
      False => case x.rule < y.rule of
        True  => prep x es
        False => y :: insertEdge ys x
      True  =>
        let (ex,ei,ey) := split x y
         in prep ex . prep ei $ insertEdge ys ey

    -- They share the same targets. We try and build one large range
    -- from the two.
    True  => case adjacent x.rule y.rule of
      False => case x.rule < y.rule of
        True  => prep x es
        False => y :: insertEdge ys x
      True  => NE (span x.rule y.rule) x.tgts :: ys

outUnion : NEdges -> NEdges -> NEdges
outUnion xs ys = foldl insertEdge ys xs

export
joinNNode : NNode a -> NNode a -> NNode a
joinNNode x y = NN x.pos (aunion x.acc y.acc) (outUnion x.out y.out)

fromEdge : Edge -> NEdge
fromEdge (E r t) = (NE r [t])

fromENode : Nat -> ENode a -> NNode a
fromENode n x = NN n x.acc $ map fromEdge x.out

covering
eclosure : Nat -> Norm a (NNode a)
eclosure x = do
  Nothing <- lookupNNode x | Just v => pure v
  n       <- getENode x
  es      <- traverse eclosure n.eps
  let nn := foldl joinNNode (fromENode x n) es
  insertNNode x nn
  pure nn

covering
closures : EGraph a -> Norm a ()
closures g = ignore $ for (keys g) eclosure

export covering
toNFA : TokenMap a -> (adj : Set32 -> RExp8 True) -> Norm a (NGraph a)
toNFA xs f = do
  toENFA xs f >>= closures
  modify {ngraph $= connectedComponent nchildren 0}
  st <- get
  pure st.ngraph

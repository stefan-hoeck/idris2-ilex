module Text.ILex.Internal.DFA

import Data.Linear.Traverse1
import Control.Monad.State
import Data.SortedMap as SM
import Text.ILex.Internal.ENFA
import Text.ILex.Internal.NFA
import Text.ILex.Internal.Types

%default total

covering
process : SnocList Edge -> NEdges -> Norm a Edges

covering
discrete : Nat -> Norm a ()
discrete x = do
  Nothing <- lookupNode x | Just v => pure ()
  nn      <- getNNode x
  ds      <- process [<] nn.out
  let nde := N nn.pos nn.acc ds
  insertNode x nde

process sx []              = pure $ (sx <>> [])
process sx (NE r ts :: xs) = do
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
          ns <- traverse getNNode set
          insertNNode t (foldl joinNNode (NN t [] []) ns)
          discrete t
          process (sx:<E r t) xs

covering
nodes : NGraph a -> Norm a ()
nodes g = for_ (keys g) discrete

normalize : Graph a -> Graph a
normalize g =
  let nm := SM.fromList . map swap $ zipWithIndex (keys g)
   in  SM.fromList . map (translate nm) $ SM.toList g

  where
    translate : SortedMap Nat Nat -> (Nat,Node a) -> (Nat,Node a)
    translate m (x, N pos acc out) =
      let tx   := safeLookup x m
       in (tx, N tx acc $ map {tgt $= (`safeLookup` m)} out)

export covering
toDFA : TokenMap a -> (adj : Set32 -> RExp8 True) -> Norm a (Graph a)
toDFA xs f = do
  toNFA xs f >>= nodes
  ng <- map ngraph get
  modify {graph $= normalize . connectedComponent children 0}
  st <- get
  pure st.graph

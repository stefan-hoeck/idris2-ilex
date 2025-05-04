module Text.ILex.Internal.ENFA

import Control.Monad.State
import Data.SortedMap
import Text.ILex.Internal.Types
import Text.ILex.RExp

%default total

--------------------------------------------------------------------------------
-- Connected Components
--------------------------------------------------------------------------------

0 Visited : Type
Visited = SortedMap Nat ()

parameters (children : a -> List Nat)
           (graph    : SortedMap Nat a)

  covering
  visit : SnocList (Nat,a) -> Visited -> List Nat -> List(Nat,a)
  visit sp v []      = sp <>> []
  visit sp v (x::xs) =
    case lookup x v of
      Just () => visit sp v xs
      Nothing =>
        let Just n := lookup x graph | Nothing => visit sp v xs
         in visit (sp:<(x,n)) (insert x () v) (children n ++ xs)

export
connectedComponent :
     (a -> List Nat)
  -> Nat
  -> SortedMap Nat a
  -> SortedMap Nat a
connectedComponent c n g =
  assert_total $ SortedMap.fromList (visit c g [<] empty [n])

--------------------------------------------------------------------------------
-- Conversion to ENFA
--------------------------------------------------------------------------------

enfa : RExp8 b -> (tgt : Nat) -> Norm a Nat
enfa Eps       tgt = pure tgt
enfa (And x y) tgt = enfa y tgt >>= enfa x
enfa (Ch x)    tgt = createENode (EN [] [] $ map (`E` tgt) $ ranges x)
enfa (Or x y)  tgt = do
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
toENFA : TokenMap8 a -> Norm a EGraph
toENFA rs = do
  ps <- traverse (\x => (,x) <$> inc) rs
  for_ ps insertTerminal
  ts <- traverse (\(n,r,c) => enfa r n) ps
  ignore $ insertENode 0 (EN [] ts [])
  st <- get
  pure st.egraph

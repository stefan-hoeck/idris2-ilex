module Text.ILex.DFA

import Data.SortedMap
import Derive.Prelude

import public Text.ILex.Expr

%default total
%language ElabReflection

||| A compiled (and now untyped) tokenizer expression
public export
data TExp : Type where
  CH      : Set -> Conv -> TExp

  And     : TExp -> TExp -> TExp

  Or      : TExp -> TExp -> TExp

  Star    : TExp -> TExp

  Epsilon : Conv -> TExp

%runElab derive "TExp" [Show,Eq]

export
outArgs : UArgs -> TExp -> Maybe UArgs
outArgs args (Epsilon x) = outArgs args x
outArgs args (CH x c)    = outArgs args c
outArgs args (And x y)   = outArgs args x >>= \as => outArgs as y
outArgs args (Or x y)    = outArgs args x <|> outArgs args y
outArgs args (Star x)    = outArgs args x

export
compile : Expr b e is os -> TExp
compile (AConv x)      = Epsilon (UC $ uconvs x)
compile (AChar {is} x) = CH x (UC $ appendChar is)
compile (AMatch x)     = CH x ID
compile (ASeq x y)     = And (compile x) (compile y)
compile (AOr x y)      = Or (compile x) (compile y)
compile (ARec x)       = Star (compile x)
compile (AFail x)      = Epsilon (EC $ [<uconv x])

--------------------------------------------------------------------------------
-- DFA State and utilities
--------------------------------------------------------------------------------

public export
record Delta where
  constructor D
  rule : Rule
  conv : Conv
  tgt  : Bits32

pre : Conv -> Delta -> Delta
pre c = {conv $= trans c}

%runElab derive "Delta" [Show,Eq]

||| State transitions in a finite, discrete automaton
public export
0 Deltas : Type
Deltas = List Delta

public export
record Node where
  constructor N
  args   : UArgs
  deltas : Deltas

%runElab derive "Node" [Show,Eq]

||| The accumulated function call graph: A mapping from
||| state to state transitions.
public export
0 Graph : Type
Graph = SortedMap Bits32 Node

-- State used for converting regular expressions to discrete
-- finite automata
record DFAState where
  constructor DFAS
  pairs : SortedMap (Bits32,Bits32) Bits32
  cur   : Bits32
  graph : Graph

inc : DFAState -> DFAState
inc = {cur $= (+1)}

insertNode : Bits32 -> Node -> DFAState -> DFAState
insertNode k n = {graph $= insert k n}

insertNodeIf : Bool -> Bits32 -> Node -> DFAState -> DFAState
insertNodeIf True  k n s = insertNode k n s
insertNodeIf False _ _ s = s

newPair : (x,y : Bits32) -> DFAState -> (DFAState, Bits32)
newPair x y s = ({cur $= (+1), pairs $= insert (x,y) s.cur} s, s.cur)

covering
merge :
     DFAState
  -> UArgs
  -> (x,y : Bits32)
  -> (rx,ry : Conv)
  -> (DFAState, Bits32, Conv)

covering
combine :
     DFAState
  -> UArgs
  -> SnocList Delta
  -> Deltas
  -> Deltas
  -> (DFAState, Deltas)
combine s args ss [] ys = (s, ss <>> ys)
combine s args ss xs [] = (s, ss <>> xs)
combine s args ss l@(x::xs) r@(y::ys) =
  case compare x.rule y.rule of
    LT => combine s args (ss:<x) xs r
    GT => combine s args (ss:<y) l  ys
    EQ =>
      let (t,n,c) := merge s args x.tgt y.tgt x.conv y.conv
       in combine t args (ss:< D x.rule c n) xs ys

merge s args x y rx ry =
  case compare x y of
    EQ => (s,x,rx)
    GT => merge s args y x ry rx
    LT =>
     let Nothing := lookup (x,y) s.pairs | Just z  => (s,z,ID)
         Just nx := lookup x s.graph     | Nothing => (s,y,ry)
         Just ny := lookup y s.graph     | Nothing => (s,x,rx)
         (t,z)   := newPair x y s
         (u,ds)  := combine t args [<] (pre rx <$> nx.deltas) (pre ry <$> ny.deltas)
      in (insertNode z (N args ds) u, z, ID)

--------------------------------------------------------------------------------
-- DFA conversion
--------------------------------------------------------------------------------

record DFARes where
  constructor DR
  state : DFAState -- current state
  rec   : Bool     -- last node recursive
  index : Bits32   -- last node
  node  : Deltas   -- last node's deltas

covering
dfa :
     UArgs
  -> DFAState
  -> (tgt  : Bits32)
  -> (post : Conv)
  -> TExp
  -> DFARes
dfa args s tgt p (CH x c) =
  DR (inc s) False s.cur [D (fromSet x) (trans c p) tgt]

dfa args s tgt p (And x y) =
 let Just out     := outArgs args x | Nothing => dfa args s tgt p x
     DR t _ iy dy := dfa out s tgt p y
  in case dy of
       [D Eps py tz] => dfa args t tz py x
       _             => dfa args (insertNode iy (N out dy) t) iy ID x

dfa args s tgt p (Or x y) =
  let DR t rx ix nx := dfa args s tgt p x
      DR u ry iy dy := dfa args t tgt p y
      (v,cs)        := combine u args [<] nx dy
      w             := insertNodeIf ry iy (N args dy) (insertNodeIf rx ix (N args nx) v)
   in DR (inc w) False w.cur cs

dfa args s tgt p (Star x) =
 let DR t _ n ds := dfa args (inc s) s.cur ID x
     (u,cs)      := combine t args [<] ds [D Eps p tgt]
  in DR u True s.cur cs

dfa args s tgt p (Epsilon c) =
  DR (inc s) False s.cur [D Eps (trans c p) tgt]

--------------------------------------------------------------------------------
-- Normalization and Pruning
--------------------------------------------------------------------------------

record NormST where
  constructor NST
  cur     : Bits32
  dict    : SortedMap Bits32 Bits32
  visited : SortedMap Bits32 ()
  nodes   : SnocList (Bits32,Node)

init : NormST
init = NST 1 (insert 0 0 empty) (insert 0 () empty) [<]

translateNode : Bits32 -> NormST -> (NormST,Bits32)
translateNode n s =
  case lookup n s.dict of
    Just x  => (s,x)
    Nothing => ({cur $= (+1), dict $= insert n s.cur} s, s.cur)

translateDeltas : SnocList Delta -> Deltas -> NormST -> (NormST,Deltas)
translateDeltas sx []           s = (s, sx <>> [])
translateDeltas sx (D r c x::xs) s =
  let (s2,y) := translateNode x s
   in translateDeltas (sx :< D r c y) xs s2

translate : Bits32 -> Node -> NormST -> NormST
translate n (N args ds) s =
  let (s2,n2)  := translateNode n s
      (s3,ds2) := translateDeltas [<] ds s2
   in {nodes  $= (:< (n2,N args ds2)), visited $= insert n ()} s3

visit : NormST -> Bits32 -> Graph -> (NormST, List Bits32)
visit s x g =
  case lookup x s.visited of
    Just () => (s, [])
    Nothing => case lookup x g of
      Nothing => (s, [])
      Just n  => (translate x n s, map tgt n.deltas)

-- runs a depth-first search, incrementally renaming and
-- accumulating all visited nodes. This prunes the graph as
-- components not reachable from the start node will be silently
-- dropped
covering
normalize : NormST -> List Bits32 -> Graph -> NormST
normalize st []        g = st
normalize st (x :: xs) g =
  let (st2,ns) := visit st x g in normalize st2 (ns++xs) g

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Converts a productive regular expression to a discrete finite automaton.
export covering
toDFA : TOnly a -> Expr b e [<] [<a] -> List (Bits32,Node)
toDFA res r =
 let cexp        := compile r
     nres        := N [<res.tpe] [D Eps ID 0]
     st          := DFAS empty 1 (insert 0 nres empty)
     DR s _ n ds := dfa [<] st 0 ID cexp
     nst         := normalize init [n] (insert n (N [<] ds) s.graph)
  in sortBy (comparing fst) $ nst.nodes <>> []

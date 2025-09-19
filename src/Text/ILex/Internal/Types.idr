module Text.ILex.Internal.Types

import public Text.ILex.RExp
import public Data.Linear.Ref1

import Data.Array.Core
import Data.Array.Index
import Data.Array.Mutable
import Data.Linear.Traverse1
import Data.Maybe
import Data.SortedMap
import Derive.Prelude
import Syntax.T1

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Mutable Maps
--------------------------------------------------------------------------------

-- TODO: This should probably go idris2-array or idris2-containers
||| A mutable map from natural numbers to values (backed by a mutable array).
|||
||| Note: Since we might need to dynamically regrow the internal array,
|||       it has to be stored as a dependent pair in a mutable reference.
export
record NatMap1 (s,a : Type) where
  constructor NM1
  ref   : Ref s (n ** MArray s n (Maybe a))

export
empty : {default 256 size : Nat} -> (0 p : IsSucc size) => F1 s (NatMap1 s a)
empty = T1.do
  arr <- marray1 size Nothing
  ref <- ref1 (size ** arr)
  pure (NM1 ref)

export
lookup1 : Nat -> NatMap1 s a -> F1 s (Maybe a)
lookup1 n m =
  read1 m.ref >>= \(sz ** vs) =>
    case tryNatToFin n of
      Just x  => Core.get vs x
      Nothing => pure Nothing

export
lookupDflt1 : Nat -> Lazy a -> NatMap1 s a -> F1 s a
lookupDflt1 n dflt m =
  read1 m.ref >>= \(sz ** vs) =>
    case tryNatToFin n of
      Just x  => Core.get vs x >>= pure . fromMaybe dflt
      Nothing => pure dflt

export
delete1 : Nat -> NatMap1 s a -> F1' s
delete1 n m =
  read1 m.ref >>= \(sz ** vs) =>
    case tryNatToFin n of
      Just x  => Core.set vs x Nothing
      Nothing => pure ()

export
insert1 : Nat -> a -> NatMap1 s a -> F1' s
insert1 n v m = read1 m.ref >>= \(_ ** vs) => go vs
  where
    go : {sz : _} -> MArray s sz (Maybe a) -> F1' s
    go vs t =
      case tryNatToFin n of
        Just x  =>
         let _ # t := Core.set vs x (Just v) t
          in write1 m.ref (_ ** vs) t
        Nothing =>
         let vs2 # t := mgrow vs sz Nothing t
          in go (assert_smaller vs vs2) t

export
fromList1 : List (Nat,a) -> F1 s (NatMap1 s a)
fromList1 ps = T1.do
  m <- empty
  traverse1_ (\(k,v) => insert1 k v m) ps
  pure m

export
pairs1 : NatMap1 s a -> F1 s (List (Nat,a))
pairs1 m = read1 m.ref >>= \(sz ** vs) => go vs [<] sz
  where
    go :
         MArray s sz (Maybe a)
      -> SnocList (Nat,a)
      -> (n : Nat)
      -> {auto 0 lte : LTE n sz}
      -> F1 s (List (Nat,a))
    go vs sv 0     t = (sv <>> []) # t
    go vs sv (S k) t =
      case getNat vs k t of
        Just v  # t => go vs (sv:<(k,v)) k t
        Nothing # t => go vs sv k t

export %inline
keys1 : NatMap1 s a -> F1 s (List Nat)
keys1 m = map fst <$> pairs1 m

export %inline
values1 : NatMap1 s a -> F1 s (List a)
values1 m = map snd <$> pairs1 m

--------------------------------------------------------------------------------
-- Connected Components
--------------------------------------------------------------------------------

parameters {sz       : Nat}
           (children : a -> List Nat)
           (visited  : MArray s sz Bool)
           (is,os    : MArray s sz (Maybe a))

  covering
  visit : List Nat -> F1' s
  visit []      t = () # t
  visit (x::xs) t =
    case tryNatToFin x of
      Nothing => visit xs t
      Just k  => case Core.get visited k t of
        True  # t => visit xs t
        False # t =>
         let _ # t := Core.set visited k True t
          in case Core.get is k t of
               Nothing   # t => visit xs t
               Just node # t =>
                let _ # t := Core.set os k (Just node) t
                 in visit (children node ++ xs) t

export
connectedComponent : (a -> List Nat) -> Nat -> NatMap1 s a -> F1' s
connectedComponent c n m =
  read1 m.ref >>= \(sz ** is) => T1.do
    vis <- marray1 sz False
    os  <- marray1 sz Nothing
    assert_total $ visit c vis is os [n]
    write1 m.ref (sz ** os)

--------------------------------------------------------------------------------
-- Node Sets
--------------------------------------------------------------------------------

public export
0 NSet : Type
NSet = List Nat

union_ : SnocList Nat -> NSet -> NSet -> NSet
union_ sx l@(x::xs) r@(y::ys) =
  case compare x y of
    LT => union_ (sx:<x) xs r
    GT => union_ (sx:<y) l  ys
    EQ => union_ (sx:<x) xs ys
union_ sx [] ys = sx <>> ys
union_ sx xs [] = sx <>> xs

export %inline
sunion : NSet -> NSet -> NSet
sunion = union_ [<]

--------------------------------------------------------------------------------
-- Call Graphs
--------------------------------------------------------------------------------

||| A transformation pointing from one node to another
public export
record Edge where
  constructor E
  ||| The characters that triggers thi conversion
  rule : Range8

  ||| The target of the given rule
  tgt  : Nat

export
transitions : Edge -> List (Bits8,Nat)
transitions (E rule tgt) =
  let l := lowerBound rule
      u := upperBound rule
   in case compare l u of
        LT => (,tgt) <$> [l..u]
        EQ => [(l,tgt)]
        GT => []

%runElab derive "Edge" [Show,Eq]

||| State transitions in a finite, discrete automaton
public export
0 Edges : Type
Edges = List Edge

public export
record ENode where
  constructor EN
  acc : List Nat
  eps : List Nat
  out : Edges

%runElab deriveIndexed "ENode" [Show]

public export
0 EGraph : Type -> Type
EGraph s = NatMap1 s ENode

||| A transformation pointing from one node to a set
||| of others
public export
record NEdge where
  constructor NE
  ||| The characters that trigger this conversion
  rule : Range8

  ||| The list of targets of the given rule
  tgts : NSet

%runElab derive "NEdge" [Show,Eq]

||| State transitions in a finite, non-discrete automaton
public export
0 NEdges : Type
NEdges = List NEdge

public export
record NNode where
  constructor NN
  pos : Nat
  acc : List Nat
  out : NEdges

%runElab deriveIndexed "NNode" [Show]

export
nchildren : NNode -> List Nat
nchildren (NN _ _ out) = out >>= tgts

public export
0 NGraph : Type -> Type
NGraph s = NatMap1 s NNode

public export
record Node where
  constructor N
  pos : Nat
  acc : List Nat
  out : Edges

%runElab deriveIndexed "Node" [Show]

export
children : Node -> List Nat
children n = tgt <$> n.out

public export
0 Graph : Type -> Type
Graph s = NatMap1 s Node

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

public export
record DFAState (s,a : Type) where
  [noHints, search s]
  constructor ST
  accs   : NatMap1 s a
  sets   : Ref s (SortedMap NSet Nat)
  egraph : EGraph s
  ngraph : NGraph s
  graph  : Graph s
  cur    : Ref s Nat

export
init : F1 s (DFAState s a)
init = T1.do
  as <- Types.empty
  ss <- ref1 SortedMap.empty
  eg <- Types.empty
  ng <- Types.empty
  g  <- Types.empty
  cr <- ref1 (S Z)
  pure (ST as ss eg ng g cr)

parameters {auto st : DFAState s a}

  export
  inc : F1 s Nat
  inc = T1.do
    n <- read1 st.cur
    write1 st.cur (S n)
    pure n

  export
  addSet : NSet -> F1 s Nat
  addSet set = T1.do
    n <- inc
    mod1 st.sets (insert set n)
    pure n

  export
  lookupSet : NSet -> F1 s (Maybe Nat)
  lookupSet set = read1 st.sets >>= pure . lookup set

  export %inline
  insertENode : Nat -> ENode -> F1 s Nat
  insertENode k n = insert1 k n st.egraph >> pure k

  export
  insertTerminal : (Nat,t,a) -> F1' s
  insertTerminal (k,_,c) = T1.do
    _ <- insertENode k (EN [k] [] [])
    insert1 k c st.accs

  export %inline
  createENode : ENode -> F1 s Nat
  createENode n = inc >>= (`insertENode` n)

  export %inline
  lookupENode : Nat -> F1 s (Maybe ENode)
  lookupENode n = lookup1 n st.egraph

  export %inline
  getENode : Nat -> F1 s ENode
  getENode n = lookupDflt1 n (EN [] [] []) st.egraph

  export %inline
  insertNNode : Nat -> NNode -> F1' s
  insertNNode k n = insert1 k n st.ngraph

  export %inline
  lookupNNode : Nat -> F1 s (Maybe NNode)
  lookupNNode n = lookup1 n st.ngraph

  export %inline
  getNNode : Nat -> F1 s NNode
  getNNode n = lookupDflt1 n (NN n [] []) st.ngraph

  export %inline
  insertNode : Nat -> Node -> F1' s
  insertNode k n = insert1 k n st.graph

  export %inline
  lookupNode : Nat -> F1 s (Maybe Node)
  lookupNode n = lookup1 n st.graph

  export %inline
  getNode : Nat -> F1 s Node
  getNode n = lookupDflt1 n (N n [] []) st.graph

  export %inline
  evalST : (forall s . DFAState s a => F1 s b) -> b
  evalST f = run1 $ init >>= \st => f @{st}

  export
  normalizeGraph : F1' s
  normalizeGraph = T1.do
    ps  <- pairs1 st.graph
    mp  <- fromList1 (map swap $ zipWithIndex $ map fst ps)
    ps2 <- traverse1 (translate mp) ps
    rs  <- fromList1 ps2
    arr <- read1 rs.ref
    write1 st.graph.ref arr

    where
     translate : NatMap1 s Nat -> (Nat,Node) -> F1 s (Nat,Node)
     translate m (x, N pos acc out) = T1.do
       x2   <- lookupDflt1 x 0 m
       out2 <- traverse1 (\(E r t) => E r <$> lookupDflt1 t 0 m) out
       pure (x2, N x2 acc out2)

||| A finite state machine with terminal states and
||| a graph representation for the state transitions.
|||
||| State 0 is the initial state.
public export
record Machine a b where
  constructor M
  terminals : SortedMap Nat a
  graph     : b

||| Evaluate a state normalizer and return the resulting
||| machine.
export
machine : (forall s . DFAState s a => F1 s b) -> Machine a b
machine f =
   run1 $ T1.do
     st  <- init
     res <- f @{st}
     ps  <- pairs1 st.accs
     pure (M (SortedMap.fromList ps) res)

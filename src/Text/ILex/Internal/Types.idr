module Text.ILex.Internal.Types

import Control.Monad.State
import Data.SortedMap
import Derive.Prelude
import public Text.ILex.RExp

%default total
%language ElabReflection

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

public export
record Acc a where
  constructor A
  tgt  : Nat
  conv : Conv a

%runElab deriveIndexed "Acc" [Show]

export
Eq (Acc a) where
  A t1 c1 == A t2 c2 = t1 == t2 && c1 == c2

public export
0 Accs : Type -> Type
Accs = List . Acc

aunion_ : SnocList (Acc a) -> Accs a -> Accs a -> Accs a
aunion_ sx l@(x::xs) r@(y::ys) =
  case compare x.tgt y.tgt of
    LT => aunion_ (sx:<x) xs r
    GT => aunion_ (sx:<y) l  ys
    EQ => aunion_ (sx:<x) xs ys
aunion_ sx [] ys = sx <>> ys
aunion_ sx xs [] = sx <>> xs

export %inline
aunion : Accs a -> Accs a -> Accs a
aunion = aunion_ [<]

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

%runElab derive "Edge" [Show,Eq]

||| State transitions in a finite, discrete automaton
public export
0 Edges : Type
Edges = List Edge

public export
record ENode a where
  constructor EN
  acc : Accs a
  eps : List Nat
  out : Edges

%runElab deriveIndexed "ENode" [Show]

public export
0 EGraph : Type -> Type
EGraph = SortedMap Nat . ENode

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
record NNode a where
  constructor NN
  pos : Nat
  acc : Accs a
  out : NEdges

%runElab deriveIndexed "NNode" [Show]

export
nchildren : NNode a -> List Nat
nchildren (NN _ _ out) = out >>= tgts

public export
0 NGraph : Type -> Type
NGraph = SortedMap Nat . NNode

public export
record Node a where
  constructor N
  pos : Nat
  acc : Accs a
  out : Edges

%runElab deriveIndexed "Node" [Show]

export
children : Node a -> List Nat
children n = tgt <$> n.out

public export
0 Graph : Type -> Type
Graph = SortedMap Nat . Node

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| For internal use only:
||| Looking up a node in a graph we are certain must be there
export
safeLookup : Nat -> SortedMap Nat a -> a
safeLookup n g =
  case SortedMap.lookup n g of
    Just v  => v
    Nothing =>
      assert_total $ idris_crash
        "Text.ILex.DFA.Internal.safeLookup returned Nothing"

public export
record NormState a where
  constructor ST
  sets   : SortedMap NSet Nat
  egraph : EGraph a
  ngraph : NGraph a
  graph  : Graph a
  cur    : Nat

public export
0 Norm : Type -> Type -> Type
Norm a b = State (NormState a) b

export
inc : Norm a Nat
inc = do
  s <- get
  put ({cur $= (+1)} s)
  pure s.cur

export
addSet : NSet -> Norm a Nat
addSet set = do
  s <- get
  modify {cur $= (+1), sets $= insert set s.cur}
  pure s.cur

export
lookupSet : NSet -> Norm a (Maybe Nat)
lookupSet set = lookup set . sets <$> get

export
insertENode : Nat -> ENode a -> Norm a Nat
insertENode k n = modify {egraph $= insert k n} $> k

export
createENode : ENode a -> Norm a Nat
createENode n = inc >>= (`insertENode` n)

export
lookupENode : Nat -> Norm a (Maybe $ ENode a)
lookupENode n = lookup n . egraph <$> get

export
getENode : Nat -> Norm a (ENode a)
getENode n = safeLookup n . egraph <$> get

export
insertNNode : Nat -> NNode a -> Norm a ()
insertNNode k n = modify {ngraph $= insert k n}

export
lookupNNode : Nat -> Norm a (Maybe $ NNode a)
lookupNNode n = lookup n . ngraph <$> get

export
getNNode : Nat -> Norm a (NNode a)
getNNode n = safeLookup n . ngraph <$> get

export
insertNode : Nat -> Node a -> Norm a ()
insertNode k n = modify {graph $= insert k n}

export
lookupNode : Nat -> Norm a (Maybe $ Node a)
lookupNode n = lookup n . graph <$> get

export
getNode : Nat -> Norm a (Node a)
getNode n = safeLookup n . graph <$> get

export
runNorm : Norm a b -> (NormState a, b)
runNorm = runState (ST empty empty empty empty 1)

export
evalNorm : Norm a b -> b
evalNorm = snd . runNorm

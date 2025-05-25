module Text.ILex.Bounds

import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Bounds
--------------------------------------------------------------------------------

||| Upper and lower bounds of a region in a byte array.
public export
data Bounds : Type where
  Empty : Bounds
  BS    : (x,y : Nat) -> (0 prf : LTE x y) => Bounds

%runElab derive "Bounds" [Show,Eq,Ord]

0 appProof :
     (u,v,x,y : Nat)
  -> {auto p1 : LTE u v}
  -> {auto p2 : LTE x y}
  -> LTE (min u x) (max v y)

app : Bounds -> Bounds -> Bounds
app Empty     y       = y
app x         Empty   = x
app (BS u v) (BS x y) = BS (min u x) (max v y) @{appProof u v x y}

export
atPos : Nat -> Bounds
atPos n = BS n n @{reflexive}

export %inline
Semigroup Bounds where (<+>) = app

export %inline
Monoid Bounds where neutral = Empty

--------------------------------------------------------------------------------
--          Bounded
--------------------------------------------------------------------------------

||| Pairs a value with the textual bounds from where it was parsed.
public export
record Bounded ty where
  constructor B
  val    : ty
  bounds : Bounds

%runElab derive "Bounded" [Show,Eq,Ord]

-- Implementation of `(<*>)`
appb : Bounded (a -> b) -> Bounded a -> Bounded b
appb (B vf b1) (B va b2) = B (vf va) (b1 <+> b2)

-- Implementation of `(>>=)`
bind : Bounded a -> (a -> Bounded b) -> Bounded b
bind (B va b1) f =
  let B vb b2 = f va
   in B vb (b1 <+> b2)

export
Functor Bounded where
  map f (B val bs) = B (f val) bs

export %inline
Applicative Bounded where
  pure v = B v neutral
  (<*>) = appb

export %inline
Monad Bounded where
  (>>=) = bind

export
Foldable Bounded where
  foldr c n b = c b.val n
  foldl c n b = c n b.val
  foldMap f b = f b.val
  null _ = False
  toList b = [b.val]

export
Traversable Bounded where
  traverse f (B v bs) = (`B` bs) <$> f v

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

0 notLTisLTE :
     (x,y : Nat)
  -> (prf : (compareNat x y == LT) === False)
  -> LTE y x
notLTisLTE 0     0     prf = LTEZero
notLTisLTE (S k) 0     prf = LTEZero
notLTisLTE (S k) (S j) prf = LTESucc (notLTisLTE k j prf)
notLTisLTE 0     (S k) prf impossible

0 notGTisLTE :
     (x,y : Nat)
  -> (prf : (compareNat x y == GT) === False)
  -> LTE x y
notGTisLTE 0     0     prf = LTEZero
notGTisLTE 0     (S k) prf = LTEZero
notGTisLTE (S k) (S j) prf = LTESucc (notGTisLTE k j prf)
notGTisLTE (S k) 0     prf impossible

0 minLemma : (u,x : Nat) -> LTE (min u x) u
minLemma u x with (compareNat u x == LT) proof eq
  _ | True  = reflexive
  _ | False = notLTisLTE u x eq

0 maxLemma : (v,y : Nat) -> LTE v (max v y)
maxLemma v y with (compareNat v y == GT) proof eq
  _ | True  = reflexive
  _ | False = notGTisLTE v y eq

appProof u v x y =
  transitive (transitive (minLemma u x) p1) (maxLemma v y)

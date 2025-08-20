||| Some utilities mainly for internal use
module Text.ILex.Internal.Runner

import Data.Array.Index
import Data.Buffer
import Data.Buffer.Core
import Data.Buffer.Mutable
import Data.Buffer.Indexed
import Data.ByteString
import Data.Maybe0
import Data.Nat.BSExtra

import Text.ILex.Bounds
import Text.ILex.Error
import Text.ILex.FC
import Text.ILex.Lexer
import Text.ILex.RExp

%default total

export
offsetToIx : (o : Nat) -> Ix s (o+s)
offsetToIx 0     = IZ
offsetToIx (S k) = rewrite plusSuccRightSucc k s in IS (offsetToIx k)

export
toByteString :
     IBuffer n
  -> (from        : Nat)
  -> (0    till   : Nat)
  -> {auto ix     : Ix (S till) n}
  -> {auto 0  lte : LTE from (ixToNat ix)}
  -> ByteString
toByteString buf from till =
  let bv := fromIBuffer buf
   in BS _ $ substringFromTo from (ixToNat ix) {lt = ixLT ix} bv

export
tillByteString :
     IBuffer n
  -> (from        : Nat)
  -> (0    till   : Nat)
  -> {auto ix     : Ix (S till) n}
  -> {auto 0  lte : LTE from (ixToNat ix)}
  -> ByteString
tillByteString buf from till =
  let bv := fromIBuffer buf
   in BS _ $ substringFromTill from (ixToNat ix) {lt2 = ixLTE ix} bv

export
toBytes :
     IBuffer n
  -> (from        : Nat)
  -> (0    to     : Nat)
  -> {auto ix     : Ix to n}
  -> {auto 0  lte : LTE from (ixToNat ix)}
  -> ByteString
toBytes buf from to =
  let bv := fromIBuffer buf
   in BS _ $ substringFromTill from (ixToNat ix) {lt2 = ixLTE ix} bv

0 ixLemmaSym : (x : Ix m n) -> m + ixToNat x === n
ixLemmaSym x = rewrite plusCommutative m (ixToNat x) in ixLemma x

0 plusLemma : (x,y : Nat) -> LTE x y -> (x+px) === (y+py) -> LTE py px
plusLemma 0     0     z Refl        = refl
plusLemma 0     (S y) z p           = rewrite p in lteSuccRight (lteAddLeft py)
plusLemma (S x) 0     z p           = absurd z
plusLemma (S x) (S y) (LTESucc z) p = plusLemma x y z (injective p)

export
0 ixImpliesLTE : Ix m n -> LTE m n
ixImpliesLTE IZ     = refl
ixImpliesLTE (IS x) = lteSuccLeft (ixImpliesLTE x)

export
0 lteImpliesIxLTE :
     LTE m n
  -> (x : Ix m k)
  -> (y : Ix n k)
  -> LTE (ixToNat y) (ixToNat x)
lteImpliesIxLTE lte x y =
 let eq1 := ixLemmaSym x
     eq2 := ixLemmaSym y
  in plusLemma m n lte (trans eq1 $ sym eq2)

export
toBS :
     IBuffer n
  -> (0 start,end : Nat)
  -> {auto x      : Ix start n}
  -> {auto y      : Ix end n}
  -> {auto 0  lt  : LT end start}
  -> ByteString
toBS buf start end =
  BS _ $ substringFromTill
    (ixToNat x)
    (ixToNat y)
    {lt1 = lteImpliesIxLTE (lteSuccLeft lt) y x}
    {lt2 = ixLTE y}
    (fromIBuffer buf)

export
toBS1 :
     MBuffer q n
  -> (0 start,end : Nat)
  -> (prev        : ByteString)
  -> {auto x      : Ix start n}
  -> {auto y      : Ix end n}
  -> {auto 0  lt  : LT end start}
  -> F1 q ByteString
toBS1 buf from till prev t =
  let ib # t := bufSubstringFromTill buf
                  (ixToNat x)
                  (ixToNat y)
                  {lt1 = lteImpliesIxLTE (lteSuccLeft lt) y x}
                  {lt2 = ixLTE y}
                  t
   in (prev <+> fromIBuffer ib) # t

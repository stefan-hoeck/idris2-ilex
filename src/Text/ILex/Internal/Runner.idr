||| Some utilities mainly for internal use
module Text.ILex.Internal.Runner

import Data.Array.Index
import Data.Buffer
import Data.Buffer.Core
import Data.Buffer.Indexed
import Data.ByteString
import Data.Linear.Ref1
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

export %inline
writeBS :
     IBuffer n
  -> (from        : Ix m n)
  -> (0    till   : Nat)
  -> {auto ix     : Ix till n}
  -> {auto 0  lte : LTE (ixToNat from) (ixToNat ix)}
  -> Ref q ByteString
  -> F1' q
writeBS buf from till ref t =
 let bv := fromIBuffer buf
     bs := BS _ $ substringFromTill (ixToNat from) (ixToNat ix) {lt2 = ixLTE ix} bv
  in write1 ref bs t

export
writeBSP :
     ByteString
  -> IBuffer n
  -> (from        : Ix m n)
  -> (0    till   : Nat)
  -> {auto ix     : Ix till n}
  -> {auto 0  lte : LTE (ixToNat from) (ixToNat ix)}
  -> Ref q ByteString
  -> F1' q
writeBSP (BS 0 _) buf from till ref t = writeBS buf from till ref t
writeBSP prev     buf from till ref t =
 let bv := fromIBuffer buf
     bs := BS _ $ substringFromTill (ixToNat from) (ixToNat ix) {lt2 = ixLTE ix} bv
  in write1 ref (prev <+> bs) t

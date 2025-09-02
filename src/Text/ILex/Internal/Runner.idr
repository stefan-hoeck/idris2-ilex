||| Some utilities mainly for internal use
module Text.ILex.Internal.Runner

import Data.Array.Index
import Data.Buffer
import Data.Buffer.Core
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
toBS :
     IBuffer n
  -> (from        : Ix m n)
  -> (0    till   : Nat)
  -> {auto ix     : Ix till n}
  -> {auto 0  lte : LTE (ixToNat from) (ixToNat ix)}
  -> ByteString
toBS buf from till =
  let bv := fromIBuffer buf
   in BS _ $ substringFromTill (ixToNat from) (ixToNat ix) {lt2 = ixLTE ix} bv

export
toBSP :
     ByteString
  -> IBuffer n
  -> (from        : Ix m n)
  -> (0    till   : Nat)
  -> {auto ix     : Ix till n}
  -> {auto 0  lte : LTE (ixToNat from) (ixToNat ix)}
  -> ByteString
toBSP (BS 0 _) buf from till = toBS buf from till
toBSP prev     buf from till = prev <+> toBS buf from till

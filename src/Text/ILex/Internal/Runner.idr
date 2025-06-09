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

||| Creates a bytestring from a buffer starting at the given offset.
export
bytes : {n : _} -> IBuffer n -> (p : Nat) -> (ix : Ix p n) => ByteString
bytes buf p = BS _ $ drop (ixToNat ix) @{ixLTE ix} (fromIBuffer buf)

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

export %inline
sp : Origin -> (l,c : Nat) -> StreamPos
sp o l c = SP o $ P l c

export
seByte : Origin -> (l,c : Nat) -> Bits8 -> StreamError t e
seByte o l c b = let p := sp o l c in SE (SB p p) (Byte b)

parameters (l : Lexer e a)

  ||| Appends the "end of input" token of a lexer (if any)
  export
  appEOI : Nat -> SnocList (Bounded a) -> Either c (List (Bounded a))
  appEOI n sb =
    case l.eoi of
      Nothing => Right $ sb <>> []
      Just v  => Right $ sb <>> [B v $ atPos n]


parameters (l         : Lexer e a)
           (start,end : StreamPos)
           (state     : Fin (S l.states))

  sappEOI : List (StreamBounded a)
  sappEOI =
    case l.eoi of
      Nothing => []
      Just v  => [B v $ SB end end]

  bounds : StreamBounds
  bounds = SB start end

  ||| Tries to read the last token of an input stream and
  ||| append it to the already accumulated list of tokens.
  export
  appLast : ByteString -> Either (StreamError a e) (List (StreamBounded a))
  appLast (BS 0 _) = Right sappEOI
  appLast bs       =
    case l.term `at` state of
      Nothing => Left (SE (SB end end) EOI)
      Just y  => case y of
        Ignore  => Right sappEOI
        Const z => Right $ B z bounds :: sappEOI
        Err x   => Left (SE bounds (Custom x))
        Txt f   => case f bs of
          Left x  => Left (SE bounds (Custom x))
          Right x => Right $ B x bounds :: sappEOI

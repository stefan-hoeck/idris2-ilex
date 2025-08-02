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

export %inline
sp : Origin -> (l,c : Nat) -> StreamPos
sp o l c = SP o $ P l c

export
seByte : Origin -> Position -> Bits8 -> StreamError t e
seByte o p b = let sp := SP o p in B (Byte b) (SB sp sp)

parameters (parser    : Parser StreamBounds e t a)
           (start,end : StreamPos)

  %inline
  sappEOI : parser.state -> Either (StreamError t e) a
  sappEOI state = parser.eoi (SB end end) state

  %inline
  bounds : StreamBounds
  bounds = SB start end

  ||| Tries to read the last token of an input stream and
  ||| append it to the already accumulated list of tokens.
  export
  appLast :
       (dfa   : DFA e t)
    -> (cur   : Maybe (Tok e t))
    -> (state : parser.state)
    -> ByteString
    -> Either (StreamError t e) a
  appLast dfa Nothing  state bs = sappEOI state
  appLast dfa (Just t) state bs =
    case t of
      Ignore    => sappEOI state
      Const v   => parser.step (I v state bounds) >>= sappEOI
      Parse f   => case f bs of
        Left  x => Left $ B (Custom x) bounds
        Right v => parser.step (I v state bounds) >>= sappEOI

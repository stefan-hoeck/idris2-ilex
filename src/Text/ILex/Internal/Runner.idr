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
seByte : Origin -> (l,c : Nat) -> Bits8 -> StreamError t e
seByte o l c b = let p := sp o l c in SE (SB p p) (Byte b)

-- parameters (l         : Lexer e c a)
--            (start,end : StreamPos)
--
--   sappEOI : DFA e c a -> Either (StreamError a e) (List (StreamBounded a))
--   sappEOI dfa =
--     case dfa.eoi of
--       Nothing        => Right []
--       Just (Right v) => Right [B v $ SB end end]
--       Just (Left v)  => Left (SE (SB end end) v)
--
--   bounds : StreamBounds
--   bounds = SB start end
--
--   ||| Tries to read the last token of an input stream and
--   ||| append it to the already accumulated list of tokens.
--   export
--   appLast :
--        (dfa   : DFA e c a)
--     -> (state : Fin (S dfa.states))
--     -> ByteString
--     -> Either (StreamError a e) (List (StreamBounded a))
--   appLast dfa state (BS 0 _) = sappEOI dfa
--   appLast dfa state bs       =
--     case dfa.term `at` state of
--       Bottom    => Left (SE (SB end end) EOI)
--       Ignore v  => sappEOI (l.dfa v)
--       Const v z => (B z bounds ::) <$> sappEOI (l.dfa v)
--       Err x   => Left (SE bounds (Custom x))
--       Txt f   => case f bs of
--         Left x  => Left (SE bounds (Custom x))
--         Right (v,x) => (B x bounds ::) <$> sappEOI (l.dfa v)

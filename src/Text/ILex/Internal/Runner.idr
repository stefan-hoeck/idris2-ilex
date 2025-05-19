||| Some utilities mainly for internal use
module Text.ILex.Internal.Runner

import Data.Array.Index
import Data.Buffer
import Data.Buffer.Core
import Data.Buffer.Indexed
import Data.ByteString

import Text.ILex.Bounds
import Text.ILex.FC
import Text.ILex.Lexer
import Text.ILex.RExp

%default total

||| Creates a bytestring from a buffer starting at the given offset.
export
bytes : {n : _} -> IBuffer n -> (p : Nat) -> (ix : Ix p n) => ByteString
bytes buf p = BS _ $ drop (ixToNat ix) @{ixLTE ix} (fromIBuffer buf)

parameters {n       : Nat}
           (o       : Origin)
           (l       : Lexer e a)
           (buf     : IBuffer n)
           (pos     : Nat)
           {auto ix : Ix pos n}

  ||| Appends the "end of input" token of a lexer (if any)
  export
  appEOI : SnocList (Bounded a) -> Either c (List (Bounded a))
  appEOI sb =
    case l.eoi of
      Nothing => Right $ sb <>> []
      Just v  => Right $ sb <>> [B v $ atPos n]

  export
  appLast :
       Fin l.states
    -> ByteString
    -> SnocList (Bounded a)
    -> Either (ParseError a e) (List (Bounded a))
  appLast cur prev sx =
    case l.term `at` cur of
      Nothing => Left (PE o (atPos n) (bytes buf pos) EOI)
      Just y  => case y of
        Ignore  => appEOI sx
        Const z => ?fooo_1
        Txt f   => ?fooo_2
        Err x   => Left (PE o ?bbbs prev x)

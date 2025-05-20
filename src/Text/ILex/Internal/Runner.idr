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

  ||| Tries to read the last token of an input stream and
  ||| append it to the already accumulated list of tokens.
  export
  appLast :
       Fin (S l.states)
    -> ByteString
    -> SnocList (Bounded a)
    -> Either (ParseError a e) (List (Bounded a))
  appLast cur prev sx =
    case l.term `at` cur of
      Nothing => Left (PE o (atPos n) (bytes buf pos) EOI)
      Just y  => case y of
        Ignore  => appEOI sx
        Const z => appEOI (sx :< B z bounds)
        Err x   => Left (PE o bounds prev (Custom x))
        Txt f   => case f prev of
          Left x  => Left (PE o bounds prev (Custom x))
          Right x => appEOI (sx :< B x bounds)

    where
      bounds : Bounds
      bounds =
       let pn := pred n
           s  := n `minus` prev.size
        in case tryLTE {n = pn} s of
             Nothing0 => Empty
             Just0 p  => BS s pn

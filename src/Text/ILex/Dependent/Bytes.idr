module Text.ILex.Dependent.Bytes

import Data.String
import Text.ILex.Char.UTF8
import public Data.ByteString
import public Text.ByteBounds
import public Text.ILex.RExp
import public Text.ILex.LTENat

%default total

||| An interface for mutable parser stacks `s` that facilitates
||| parsing string tokens containing escape sequences.
public export
data Bytes : (n : Nat) -> Type where
  [noHints]
  BS :
       {n : _}
    -- Remainder of the previous bytestring that should
    -- be used as the beginning of the current token.
    -> (prev : ByteString)

    -- The byte vector currently being processed.
    -> (cur  : IBuffer n)

    -- Absolute position of the first byte of `prev`.
    -> (prevOffset : Nat)

    -- Absolute position of the first byte of `cur`
    -- (this equals `prevOffset + prev.size` but should be
    -- provided as a separate field for reasons of efficiency)
    -> (curOffset  : Nat)
    -> Bytes n

||| Initializes a new parser stack.
public export
init : {n : _} -> IBuffer n -> Bytes n
init buf = BS empty buf 0 0

public export
newBytes : {n : _} -> (offset : Nat) -> ByteString -> IBuffer n -> Bytes n
newBytes o bs buf =
  BS
    { cur        = buf
    , prev       = bs
    , prevOffset = o
    , curOffset  = o + bs.size
    }

public export
record In a where
  constructor I
  {0 size : Nat}

  bytes : Bytes size

  ||| Lower relative token bound (lower position in `cur`)
  from  : LTENat size

  ||| Next relative token bound (upser position + 1 in `cur`)
  till  : LTENat size

  val   : a

||| Returns the current substring of the byte vector
||| (corresponding to the position and length of the current
||| token).
|||
||| The remainder of the previous bytestring is prefixed in case
||| we are currently at position zero.
export %inline
getBytes : In a -> ByteString
getBytes (I (BS p c po co) rf rt _) =
  case rf.val of
    0 => p <+> bytesFromTill c rf rt
    _ => bytesFromTill c rf rt

export %inline
getString : In a -> String
getString (I (BS p c po co) rf rt _) =
  case rf.val of
    0 => toString $ p <+> bytesFromTill c rf rt
    _ => stringFromTill c rf rt

export %inline
toFinalPos' : Bytes n -> a -> In a
toFinalPos' bs@(BS {}) = I bs (last n) (last n)

export %inline
toFinalPos : In a -> In a
toFinalPos (I bs@(BS {n} {}) _ _ v) = I bs (last n) (last n) v

||| Gets the absolute position of the
||| first byte of the current token.
export %inline
startPos : In a -> BytePos
startPos (I (BS p c po co) (LN f) _ _) =
  case f of
    0 => BP po
    _ => BP $ co + f

||| Gets the absolute position of the last byte of the current token.
export %inline
endPos : In a -> BytePos
endPos (I (BS p c po co) (LN rf) (LN rt) _) =
  case rf of
    0 => endPos po      (co+rt)
    _ => endPos (co+rf) (co+rt)

||| Gets the bounds of the current token.
export %inline
bounds : In a -> ByteBounds
bounds (I (BS p c po co) (LN rf) (LN rt) _) =
  let till := co + rt
   in case rf of
        0 => let from := po      in BB (BP from) (endPos from till)
        _ => let from := co + rf in BB (BP from) (endPos from till)

||| Computes the given value and pairs it with the token bounds.
export %inline
bounded : In a -> t -> ByteBounded t
bounded x v = B v $ Bytes.bounds x

||| Like `failWith`, but generates the bounds of the error from the
||| current position and the bytes read until the error occurred.
export %inline
failHere : In a -> InnerError e -> BBErr e
failHere = bounded

export
unexpectedInner : List String -> In a -> InnerError e
unexpectedInner ss i =
  case getBytes i of
    BS 0 _  => EOI
    BS 1 bv =>
     let b := bv `at` 0
         s := String.singleton (cast b)
      in case isAscii b of
           True  => Expected ss s
           False => InvalidByte b
    bs => Expected ss (toString bs)

export
unexpectedErr : List String -> In a -> BBErr e
unexpectedErr ss i = failHere i $ unexpectedInner ss i

export
unclosedErr : ByteBounds -> String -> BBErr e
unclosedErr bnds str = B (Unclosed str) bnds

export
failUnexpected : List String -> In a -> Either (BBErr e) x
failUnexpected ss = Left . unexpectedErr ss

export
failUnclosed : ByteBounds -> String -> Either (BBErr e) x
failUnclosed bnds = Left . unclosedErr bnds

module Text.ILex.LTENat

import public Data.ByteString

%default total

public export
record LTENat (n : Nat) where
  constructor LN
  val : Nat
  {auto 0 prf : LTE val n}

export %inline
lteNat : (0 m : Nat) -> Ix m n => LTENat n
lteNat _ @{x} = LN (ixToNat x) @{ixLTE x}

export %inline
first : (0 n : Nat) -> LTENat n
first n = LN 0

export %inline
last : (n : Nat) -> LTENat n
last n = LN n

export %inline
bytesFromTill : IBuffer n -> (from, till : LTENat n) -> ByteString
bytesFromTill buf (LN from @{lt1}) (LN till @{lt2}) =
  BS (till `minus` from) (BV buf from $ plusMinusBothLTE _ _ lt1 lt2)

export %inline
stringFromTill : IBuffer n -> (from, till : LTENat n) -> String
stringFromTill buf (LN from @{lt1}) (LN till @{lt2}) =
  toString buf from (till `minus` from) @{plusMinusBothLTE _ _ lt1 lt2}

module Text.ILex.Char.UTF8

import Data.Bits
import Derive.Prelude
import Text.ILex.RExp

%default total
%language ElabReflection

public export
record Codepoint where
  constructor CP
  0 len   : Nat
  bytes : Vect (S len) Bits8

go : (pre : Bits8) -> (n : Nat) -> Bits32 -> Vect n Bits8
go pre 0     m = []
go pre (S k) m =
  (pre + cast (prim__shr_Bits32 m (cast k * 6) .&. 63)) :: go 128 k m

encode : Bits32 -> Codepoint
encode x =
  if      x < 0x80    then CP 0 [cast x]
  else if x < 0x800   then CP 1 $ go 0b1100_0000 _ x
  else if x < 0x10000 then CP 2 $ go 0b1110_0000 _ x
  else                     CP 3 $ go 0b1111_0000 _ x

hexChar : Bits8 -> Char
hexChar 0  = '0'
hexChar 1  = '1'
hexChar 2  = '2'
hexChar 3  = '3'
hexChar 4  = '4'
hexChar 5  = '5'
hexChar 6  = '6'
hexChar 7  = '7'
hexChar 8  = '8'
hexChar 9  = '9'
hexChar 10 = 'a'
hexChar 11 = 'b'
hexChar 12 = 'c'
hexChar 13 = 'd'
hexChar 14 = 'e'
hexChar _  = 'f'

export
toHex : Bits8 -> String
toHex x = pack ['0','x',hexChar (shiftR x 4), hexChar (x .&. 15)]

pretty : Codepoint -> String
pretty (CP _ m) = fastConcat . intersperse "_" . map toHex $ toList m

toUTF : String -> String
toUTF =
     fastConcat
   . intersperse " "
   . map (pretty . encode . cast)
   . unpack

test : String
test = "The quick brown 🦊 jumps over 13 lazy 🐶."

public export
record Span where
  constructor SP
  {0 len : Nat}
  c1 : Vect (S len) Bits8
  c2 : Vect (S len) Bits8

encodeSP : (n : Bits32) -> Vect (S $ len $ encode n) Bits8
encodeSP n = bytes $ encode n

partial
spans : Vect m Bits8 -> Vect n Bits8 -> List Span
spans x@[_]       y@[_]       = [SP x y]
spans x@[_,_]     y@[_,_]     = [SP x y]
spans x@[_,_,_]   y@[_,_,_]   = [SP x y]
spans x@[_,_,_,_] y@[_,_,_,_] = [SP x y]
spans x@[_]       y = SP x (encodeSP 0x7f) :: spans (encodeSP 0x80) y
spans x@[_,_]     y = SP x (encodeSP 0x7ff) :: spans (encodeSP 0x800) y
spans x@[_,_,_]   y = SP x (encodeSP 0xffff) :: spans (encodeSP 0x10000) y

--------------------------------------------------------------------------------
-- UTF-8 ranges
--------------------------------------------------------------------------------

-- minimum and maximum additional (non-leading) UTF-8 bytes in
-- multi-byte code points.
MinAddByte, MaxAddByte : Bits8
MinAddByte = 0b1000_0000
MaxAddByte = 0b1011_1111

bytes : (x,y : Bits8) -> RExp8 True
bytes x y = Ch (range $ range (cast x) (cast y))

anyBytes : Vect (S n) Bits8 -> RExp8 True
anyBytes [_]              = bytes MinAddByte MaxAddByte
anyBytes (_ :: xs@(_::_)) = bytes MinAddByte MaxAddByte >> anyBytes xs

fromSpan : Span -> RExp8 True
fromSpan (SP xs ys) = go xs ys
  where
    go : Vect (S n) Bits8 -> Vect (S n) Bits8 -> RExp8 True
    go [x]     [y]                   = bytes x y
    go (x::xs@(_::_)) (y::ys@(_::_)) =
      case x == y of
        True  => bytes x x >> go xs ys
        False =>
          let r1 := bytes x x >> go xs (ys $> MaxAddByte)
              r2 := bytes y y >> go (xs $> MinAddByte) ys
           in case x+1 < y of
                False => r1 <|> r2
                True  => r1 <|> r2 <|> (bytes (x+1) (y-1) >> anyBytes xs)

fromRange : Range32 -> RExp8 True
fromRange r =
  case isEmpty r of
    True  => Ch empty
    False => assert_total $
      case spans (encodeSP $ lowerBound r) (encodeSP $ upperBound r) of
        []      => Ch empty
        (s::ss) => foldr (\x,y => fromSpan x <|> y) (fromSpan s) ss

convert : List Range32 -> RExp8 True
convert []        = Ch empty
convert (x :: xs) = foldr (\r,y => fromRange r <|> y) (fromRange x) xs

export
toByteRanges : Set32 -> RExp8 True
toByteRanges = convert . ranges . intersection unicode

export
toUTF8 : (RExp b, a) -> (RExp8 b, a)
toUTF8 (x,v) = (adjRanges toByteRanges x, v)

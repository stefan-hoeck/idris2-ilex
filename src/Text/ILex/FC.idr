module Text.ILex.FC

import Data.ByteString
import Derive.Prelude
import Text.ILex.Bounds

%default total
%language ElabReflection

public export
data Origin : Type where
  FileSrc : (path : String) -> Origin
  Virtual : Origin

%runElab derive "Origin" [Show,Eq]

public export
Interpolation Origin where
  interpolate (FileSrc p) = p
  interpolate Virtual     = "virtual"

||| Character position (line and column) in a string
public export
record Position where
  constructor P
  line   : Nat
  column : Nat

%runElab derive "Position" [Show,Eq]

public export
Interpolation Position where
  interpolate (P l c) = show (l+1) ++ ":" ++ show (c+1)

public export
record FileContext where
  constructor FC
  origin : Origin
  start  : Position
  end    : Position

export
Interpolation FileContext where
  interpolate (FC o s e) =
    if s == e
       then "\{o}: \{s}"
       else "\{o}: \{s}--\{e}"

nextRem : Fin 4 -> Bits8 -> Fin 4
nextRem FZ     m =
  if      m < 0b1000_0000  then 0
  else if m < 0b1110_0000  then 1
  else if m < 0b1111_0000  then 2
  else                          3
nextRem (FS x) m = weaken x

||| Converts an index into a bytestring to a position
||| (line and column) in the corresponding UTF-8 string.
export
toPosition : Nat -> ByteString -> Position
toPosition n (BS x bv) = go 0 0 x 0
  where
    -- we iterate over a bytestring of UTF-8 encoded characters
    -- if we are in the middle of a character, we continue until
    -- the end of character is encountered.
    go : (l,c : Nat) -> (n : Nat) -> Fin 4 -> (y : Ix n x) => Position
    go l c 0     _   = P l c
    go l c (S k) rem =
      let byte := bv `ix` k
          nxt  := nextRem rem byte
       in case nxt of
            0 => case ixToNat y >= n of
              True  => P l c
              False => case byte of
                0x0a => go (l+1) 0     k nxt
                _    => go l     (c+1) k nxt
            _ => go l c k nxt

range : Nat -> Nat -> List a -> List a
range s e = take ((e `minus` s) + 1) . drop s

lineNumbers : SnocList String -> Nat -> Nat -> List String -> SnocList String
lineNumbers sl _ _    []     = sl
lineNumbers sl size n (h::t) =
  let k   := S n
      pre := padLeft size '0' $ show k
   in lineNumbers (sl :< " \{pre} | \{h}") size k t

export
printFC : FileContext -> (sourceLines : List String) -> List String
printFC fc@(FC o (P sr sc) (P er ec)) ls =
  let  nsize  := length $ show (er + 1)
       head   := "\{fc}"
   in case sr == er of
     False =>
       lineNumbers [<"",head] nsize sr (range sr (min er $ sr+5) ls) <>> []
     True  =>
       let -- In case of end-of-input errors, we sometimes get `ec == sc`.
           -- We want to make sure we still print at least one emphasis character
           -- in those cases.
           cemph := max 1 (ec `minus` sc)
           emph  := indent (nsize + sc + 4) (replicate cemph '^')
           fr    := er `minus` 4 -- first row
        in lineNumbers [<"",head] nsize fr (range fr er ls) <>> [emph]

--------------------------------------------------------------------------------
--          Stream Bounds
--------------------------------------------------------------------------------

public export
record StreamPos where
  constructor SP
  origin   : Origin
  position : Position

zeroPos : StreamPos
zeroPos = SP Virtual (P 0 0)

%runElab derive "StreamPos" [Show,Eq]

public export
record StreamBounds where
  constructor SB
  start : StreamPos
  end   : StreamPos

export
zero : StreamBounds
zero = SB zeroPos zeroPos

%runElab derive "StreamBounds" [Show,Eq]

export
Interpolation StreamBounds where
  interpolate (SB (SP o1 p1) (SP o2 p2)) =
    case o1 == o2 of
      True  =>
        """
        \{FC o1 p1 p2}
        """
      False =>
        """
        \{FC o1 p1 p1} -
        \{FC o2 p2 p2}
        """

public export
0 StreamBounded : Type -> Type
StreamBounded = GenBounded StreamBounds

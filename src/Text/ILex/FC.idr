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

public export
record FileContext where
  constructor FC
  origin : Origin
  bounds : Bounds

export
Interpolation FileContext where
  interpolate (FC o Empty)    = interpolate o
  interpolate (FC o $ BS s e) =
    if s == e
       then "\{o}: \{s}"
       else "\{o}: \{s}--\{e}"

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
printFC fc@(FC o Empty) ls =
  let head   := "\{fc}"
   in lineNumbers [<"",head] 1 0 (range 0 0 ls) <>> []
printFC fc@(FC o $ BS (P sr sc) (P er ec)) ls =
  let  nsize  := length $ show (er + 1)
       head   := "\{fc}"
   in case sr == er of
     False =>
       lineNumbers [<"",head] nsize sr (range sr (min er $ sr+5) ls) <>> []
     True  =>
       let cemph := S $ ec `minus` sc
           emph  := indent (nsize + sc + 4) (replicate cemph '^')
           fr    := er `minus` 4 -- first row
        in lineNumbers [<"",head] nsize fr (range fr er ls) <>> [emph]

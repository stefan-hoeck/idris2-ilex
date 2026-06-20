module Text.ILex.FS

import Data.Buffer
import public FS
import public Text.ILex
import Syntax.T1
import Text.ILex.Char.UTF8

%default total

||| Converts a stream of byte strings to a list of tokens of
||| type `a`.
|||
||| This can be used with any non-backtracking parsers, but for large
||| amounts of data, the mutable parser stack must accumulate completely
||| parsed values and emit them after every chunk of bytes has been
||| processed.
export
streamParse :
     {auto has : Has (BBErr e) es}
  -> {auto lft : ELift1 q f}
  -> (prs      : P1 q (BBErr e) a)
  -> Pull f ByteString es x
  -> Pull f a es x
streamParse prs pl = Prelude.do
  st      <- lift1 (init prs)
  go st pl

  where
    go : LexState prs -> Pull f ByteString es x -> Pull f a es x
    go st p =
      assert_total $ P.uncons p >>= \case
        Left res      => Prelude.do
          v <- eliftEither {s = q} (lastStep prs st)
          emit v $> res
        Right (BS n bv,p2) => Prelude.do
          st2 <- eliftEither (stepState (toIBuffer bv) prs st)
          m   <- lift1 (prs.chunk st2.stack)
          consMaybe m (go st2 p2)

export %inline
streamVal :
     {auto has : Has (BBErr e) es}
  -> {auto lft : ELift1 q f}
  -> (dflts : Lazy a)
  -> (prs : P1 q (BBErr e) a)
  -> Stream f es ByteString
  -> Pull f o es a
streamVal dflt prs = P.lastOr dflt . streamParse prs

--------------------------------------------------------------------------------
-- Error Handling
--------------------------------------------------------------------------------

module Text.ILex.FS

import Data.Buffer
import public FS
import public Text.ILex
import Syntax.T1
import Text.ILex.Char.UTF8

%hide Data.Linear.(.)
%default total

||| Converts a stream of byte strings to a list of tokens of
||| type `a`.
|||
||| This can be used with any non-backtracking parsers, but for large
||| amounts of data, the mutable parser stack must accumulate completely
||| parsed values and emit them after every chunk of bytes has been
||| processed.
export
streamParseErr :
     {auto has : Has ex es}
  -> {auto lft : ELift1 q f}
  -> (err      : e -> ex)
  -> (prs      : P1 q e a)
  -> Pull f ByteString es x
  -> Pull f a es x
streamParseErr err prs pl = Prelude.do
  st      <- lift1 (init prs)
  go st pl

  where
    onErr : HSum [e] -> HSum es
    onErr (Here x) = inject (err x)

    go : LexState prs -> Pull f ByteString es x -> Pull f a es x
    go st p =
      assert_total $ P.uncons p >>= \case
        Left res      => Prelude.do
          v <- mapErrors onErr $ eliftEither {s = q} (lastStep prs st)
          emit v $> res
        Right (BS n bv,p2) => Prelude.do
          st2 <- mapErrors onErr $ eliftEither (stepState (toIBuffer bv) prs st)
          m   <- lift1 (prs.chunk st2.stack)
          consMaybe m (go st2 p2)

||| Converts a stream of byte strings to a list of tokens of
||| type `a`.
|||
||| This can be used with any non-backtracking parsers, but for large
||| amounts of data, the mutable parser stack must accumulate completely
||| parsed values and emit them after every chunk of bytes has been
||| processed.
export %inline
streamParse :
     {auto has : Has e es}
  -> {auto lft : ELift1 q f}
  -> (prs      : P1 q e a)
  -> Pull f ByteString es x
  -> Pull f a es x
streamParse = streamParseErr id

export %inline
streamValErr :
     {auto has : Has ex es}
  -> {auto lft : ELift1 q f}
  -> (err   : e -> ex)
  -> (dflts : Lazy a)
  -> (prs : P1 q e a)
  -> Stream f es ByteString
  -> Pull f o es a
streamValErr err dflt prs = P.lastOr dflt . streamParseErr err prs

export %inline
streamVal :
     {auto has : Has e es}
  -> {auto lft : ELift1 q f}
  -> (dflts : Lazy a)
  -> (prs : P1 q e a)
  -> Stream f es ByteString
  -> Pull f o es a
streamVal = streamValErr id

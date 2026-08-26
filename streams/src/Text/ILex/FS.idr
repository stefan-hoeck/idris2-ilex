module Text.ILex.FS

import Data.Buffer
import Data.SnocList
import Syntax.T1
import Text.ByteRange
import Text.ILex.Char.UTF8
import public FS.Posix
import public Text.ILex

%hide Data.Linear.(.)
%default total

||| Converts a stream of byte strings to a list of tokens of
||| type `a`.
|||
||| This can be used with any non-backtracking parsers, but for large
||| amounts of data, the mutable parser stack must accumulate completely
||| parsed values and emit them after every chunk of bytes has been
||| processed in order not to overflow system memory.
export
streamParseErr :
     {auto has : Has ex es}
  -> {auto lft : ELift1 q f}
  -> (err      : e -> ex)
  -> (prs      : P1 q e a)
  -> Pull f ByteString es x
  -> Pull f a es x
streamParseErr err prs pl = Prelude.do
  st      <- lift1 (init 0 empty prs)
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

||| Like `streamParseErr`, where the parse error is converted to
||| an error of type `ByteError e`.
export %inline
streamParseFrom :
     {auto has : Has (ByteError e) es}
  -> {auto lft : ELift1 q f}
  -> Origin
  -> (prs      : P1 q (ByteBounded e) a)
  -> Pull f ByteString es x
  -> Pull f a es x
streamParseFrom o = streamParseErr (byteError o)

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

||| Runs a non-streaming parser to completion, emitting
||| the last (and only) emitted value or the given default value.
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
streamValFrom :
     {auto has : Has (ByteError e) es}
  -> {auto lft : ELift1 q f}
  -> Origin
  -> (dflts : Lazy a)
  -> (prs : P1 q (ByteBounded e) a)
  -> Stream f es ByteString
  -> Pull f o es a
streamValFrom o = streamValErr (byteError o)

export %inline
streamVal :
     {auto has : Has e es}
  -> {auto lft : ELift1 q f}
  -> (dflts : Lazy a)
  -> (prs : P1 q e a)
  -> Stream f es ByteString
  -> Pull f o es a
streamVal = streamValErr id

--------------------------------------------------------------------------------
-- Error Localization
--------------------------------------------------------------------------------

||| Re-runs a stream of bytes to provide proper text bounds
||| (start and end line as well as start and end column)
||| of some byte bounds.
export
locateBounds :
     {auto h : HasIO (f es)}
  -> ByteBounds
  -> Stream f es ByteString
  -> Pull f o es (Maybe TextBounds)
locateBounds NoBB           bs = pure Nothing
locateBounds (BB start end) bs =
     P.scans1 None (appendChunk start end) bs
  |> P.takeThrough (not . isDone)
  |> P.lastOr None
  |> map (textBounds start end)

parameters {auto ph : PollH e}
           {auto he : Has Errno es}
           (0 x     : Type)
           {auto hb : Has (ByteError x) es}
           {auto hf : Has (FCErr x) es}

  ||| Streams again the origin (if any) of a parsing error,
  ||| adding the content to the error in order to provide an
  ||| exact error location.
  |||
  ||| Attention: This will try and read the whole content of the
  ||| origin into memory! If you are streaming a truly huge file,
  ||| you will be better off with just accepting the less precise
  ||| error message with only the byte bounds of the erroneous token.
  export
  locError : AsyncPull e o es a -> AsyncPull e o es a
  locError =
    handleError (ByteError x) $ \x => case x.origin of
      FileSrc p => Prelude.do
        m <- locateBounds x.bounds (readBytes p)
        maybe (throw x) (throw . toFCErr x) m
      Virtual   => throw x

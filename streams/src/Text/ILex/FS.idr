module Text.ILex.FS

import Data.Buffer
import public FS
import public Text.ILex.Bytes
import Syntax.T1
import Text.ILex.Char.UTF8
import Text.ILex.Internal.Runner
import Text.ILex.Runner1

%default total

parameters (p : P1 q e a)

  ||| Tries to read the last token of an input stream and
  ||| append it to the already accumulated list of tokens.
  export
  appLast : ByteString -> PIx p -> PST p -> Maybe (PStep p) -> F1 q (Either e a)
  appLast bs st sk tok =
    case bs of
      BS 0 _ => p.eoi bs st sk
      _      => case tok of
        Just f  => lastStep p f st bs sk
        Nothing => fail p st bs sk

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
  -> Origin
  -> Pull f ByteString es x
  -> Pull f a es x
streamParse prs o pl = Prelude.do
  st      <- lift1 (init prs)
  go st pl

  where
    go :
         LexState prs
      -> Pull f ByteString es x
      -> Pull f a es x
    go st p =
      assert_total $ P.uncons p >>= \case
        Left res      =>
          lift1 {s = q} (appLast prs st.bytes st.state st.stack st.tok) >>= \case
            Left x  => throw x
            Right v => emit v $> res
        Right (bs1,p2) => Prelude.do
          lift1 (pparseBytes prs st bs1) >>= \case
            Left x        => throw x
            Right (st2,m) => consMaybe m (go st2 p2)

export %inline
streamVal :
     {auto has : Has (BBErr e) es}
  -> {auto lft : ELift1 q f}
  -> (dflts : Lazy a)
  -> (prs : P1 q (BBErr e) a)
  -> Origin
  -> Stream f es ByteString
  -> Pull f o es a
streamVal dflt prs o = P.lastOr dflt . streamParse prs o

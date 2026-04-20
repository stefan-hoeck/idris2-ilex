module Text.ILex.FS

import public FS
import public Text.ILex
import Syntax.T1
import Text.ILex.Char.UTF8
import Text.ILex.Internal.Runner
import Text.ILex.Runner1

%default total

parameters (p : P1 q e a)

  ||| Tries to read the last token of an input stream and
  ||| append it to the already accumulated list of tokens.
  export
  appLast : PIx p -> PST p -> Maybe (PStep p) -> F1 q (Either e a)
  appLast st sk tok =
    read1 (bytes @{p.hasb} sk) >>= \case
      BS 0 _ => p.eoi st sk
      _      => case tok of
        Just f  => lastStep p f st sk
        Nothing => fail p st sk

||| Converts a stream of byte strings to a list of tokens of
||| type `a`.
|||
||| This can be used with any non-backtracking parsers, but for large
||| amounts of data, the mutable parser stack must accumulate completely
||| parsed values and emit them after every chunk of bytes has been
||| processed.
export
streamParse :
     {auto has : Has (ParseError e) es}
  -> {auto lft : ELift1 q f}
  -> (prs      : P1 q (BoundedErr e) a)
  -> {auto hap : HasPosition prs.state}
  -> Origin
  -> Pull f ByteString es x
  -> Pull f a es x
streamParse prs o pl = Prelude.do
  st      <- lift1 (init prs)
  posprev <- lift1 {s = q} (getPosition @{st.stack} @{hap})
  prev    <- readref {s = q} (bytes @{prs.hasb} st.stack)
  go prev posprev empty st pl

  where
    toErr : ByteString -> Position -> ByteString -> BoundedErr e -> ParseError e
    toErr prev posprev bs (B x bnds) =
     -- We are in the middle of an UTF-8-encoded byte sequence.
     -- If we start with the remainder of a multi-byte codepoint,
     -- we drop the corresponding bytes and increas the position's
     -- column by one.
     let pos  := incBytes prev posprev
         bs'  := dropWhile (not . isStartByte) bs
         pos' := if bs'.size < bs.size then incCol pos else pos
      in PE o bnds (bnds `relativeTo` pos') (Just $ toString bs') x

    -- Position and ByteString correspond to the previously processed
    -- chunk of data and the text position of its first byte. This is
    -- used to print the error context in case of an excpetion. If tokens
    -- can be larger than a single chunk of data, this might not be enough
    -- to print a proper error context.
    go :
         (prev0    : ByteString)
      -> (posprev0 : Position)
      -> (bs0      : ByteString)
      -> LexState prs
      -> Pull f ByteString es x
      -> Pull f a es x
    go prev0 posprev0 bs0 st p =
      assert_total $ P.uncons p >>= \case
        Left res      =>
          lift1 {s = q} (appLast prs st.state st.stack st.tok) >>= \case
            Left x  => throw (toErr prev0 posprev0 bs0 x)
            Right v => emit v $> res
        Right (bs1,p2) => Prelude.do
          posprev1 <- lift1 {s = q} (getPosition @{st.stack} @{hap})
          prev1    <- readref {s = q} (bytes @{prs.hasb} st.stack)
          lift1 (pparseBytes prs st bs1) >>= \case
            Left x        => throw (toErr prev0 posprev0 (bs0 <+> bs1) x)
            Right (st2,m) => consMaybe m (go prev1 posprev1 bs1 st2 p2)

export %inline
streamVal :
     {auto has : Has (ParseError e) es}
  -> {auto lft : ELift1 q f}
  -> (dflts : Lazy a)
  -> (prs : P1 q (BoundedErr e) a)
  -> {auto hap : HasPosition prs.state}
  -> {auto hab : HasBytes prs.state}
  -> Origin
  -> Stream f es ByteString
  -> Pull f o es a
streamVal dflt prs o = P.lastOr dflt . streamParse prs o

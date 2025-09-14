module Text.ILex.FS

import public FS
import public Text.ILex
import Syntax.T1
import Text.ILex.Char.UTF8
import Text.ILex.Internal.Runner
import Text.ILex.Runner1

%default total

parameters (p : P1 q e r s a)

  ||| Tries to read the last token of an input stream and
  ||| append it to the already accumulated list of tokens.
  export
  appLast : Index r -> s q -> Maybe (Step1 q r s) -> F1 q (Either e a)
  appLast st sk tok =
    read1 (bytes @{p.hasb} sk) >>= \case
      BS 0 _ => p.eoi st sk
      _      => case tok of
        Just f  => lastStep p f st sk
        Nothing => fail p st sk

export
streamParse :
     {auto has : Has (ParseError e) es}
  -> {auto lft : ELift1 q f}
  -> {auto hap : HasPosition s}
  -> P1 q (BoundedErr e) r s a
  -> Origin
  -> Pull f ByteString es x
  -> Pull f a es x
streamParse prs o pl = Prelude.do
  st  <- lift1 (init prs)
  pos <- lift1 (getPosition @{st.stack})
  go pos empty st pl

  where
    toErr : Position -> ByteString -> BoundedErr e -> ParseError e
    toErr pos bs (B x bnds) =
     -- We are in the middle of an UTF-8-encoded byte sequence.
     -- If we start with the remainder of a multi-byte codepoint,
     -- we drop the corresponding bytes and increas the position's
     -- column by one.
     let bs'  := dropWhile (not . isStartByte) bs
         pos' := if bs'.size < bs.size then incCol 1 pos else pos
      in toParseError o (toString bs') (B x $ bnds `relativeTo` pos')

    go :
         Position
      -> ByteString
      -> LexState q (BoundedErr e) r s
      -> Pull f ByteString es x
      -> Pull f a es x
    go pos prev st p =
      assert_total $ P.uncons p >>= \case
        Left res      =>
          lift1 (appLast prs st.state st.stack st.tok) >>= \case
            Left x  => throw (toErr pos prev x)
            Right v => emit v $> res
        Right (bs,p2) =>
          lift1 (pparseBytes prs st bs) >>= \case
            Left x        => throw (toErr pos (prev <+> bs) x)
            Right (st2,m) => Prelude.do
              pos <- lift1 (getPosition @{st.stack})
              consMaybe m (go pos bs st2 p2)

export %inline
streamVal :
     {auto has : Has (ParseError e) es}
  -> {auto lft : ELift1 q f}
  -> {auto hap : HasPosition s}
  -> (dflts : Lazy a)
  -> P1 q (BoundedErr e) r s a
  -> Origin
  -> Stream f es ByteString
  -> Pull f o es a
streamVal dflt prs o = P.lastOr dflt . streamParse prs o

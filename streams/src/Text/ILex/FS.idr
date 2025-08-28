module Text.ILex.FS

import public FS
import public Text.ILex.Parser
import Text.ILex.Internal.Runner
import Text.ILex.Runner1

%default total

parameters (p : P1 q e r s a)

  ||| Tries to read the last token of an input stream and
  ||| append it to the already accumulated list of tokens.
  export
  appLast :
       r
    -> s q
    -> Step1 q e r s
    -> ByteString
    -> F1 q (Either e a)
  appLast st sk _ (BS 0 _) t = P1.eoi p st sk t
  appLast st sk v bs       t = lastStep p v st sk bs t

export
streamParse :
     {auto has : Has e es}
  -> {auto lft : ELift1 q f}
  -> P1 q e r s a
  -> Pull f ByteString es x
  -> Pull f a es x
streamParse prs pl = lift1 (init prs) >>= flip go pl
  where
    go : LexState q e r s -> Pull f ByteString es x -> Pull f a es x
    go st p =
      assert_total $ P.uncons p >>= \case
        Left res      =>
          lift1 (appLast prs st.state st.stack st.tok st.prev) >>= \case
            Left err => throw err
            Right v  => emit v $> res
        Right (bs,p2) =>
          lift1 (pparseBytes prs st bs) >>= \case
            Left x        => throw x
            Right (st2,m) => consMaybe m (go st2 p2)

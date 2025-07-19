module Text.ILex.FS

import Text.ILex.Internal.Runner

import public FS
import public Text.ILex

import Derive.Prelude

%default total
%language ElabReflection

export
streamLex :
     {auto has : Has (StreamError t e) es}
  -> Parser StreamBounds e t a
  -> Pull f (Origin,ByteString) es r
  -> Pull f a es r
streamLex prs = go (init Virtual prs)
  where
    go :
         LexState e prs.state t
      -> Pull f (Origin,ByteString) es r
      -> Pull f a es r
    go st p =
      assert_total $ P.uncons p >>= \case
        Left res      =>
          case appLast prs st.pos st.end st.dfa st.cur st.state st.prev of
            Left err => throw err
            Right v  => emit v $> res
        Right ((o,bs),p2) => case plexBytes prs o st bs of
          Left err      => throw err
          Right (st2,m) => consMaybe m (go st2 p2)


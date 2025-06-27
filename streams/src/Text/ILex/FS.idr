module Text.ILex.FS

import Text.ILex.Internal.Runner

import public FS
import public Text.ILex

import Derive.Prelude

%default total
%language ElabReflection

export
streamLex :
     {auto has : Has (StreamError a e) es}
  -> Lexer e c a
  -> Pull f (Origin,ByteString) es r
  -> Pull f (List $ StreamBounded a) es r
streamLex l = go (init Virtual)
  where
    go :
         LexState l.states
      -> Pull f (Origin,ByteString) es r
      -> Pull f (List $ StreamBounded a) es r
    go st p =
      assert_total $ P.uncons p >>= \case
        Left res      => case appLast l st.pos st.end st.cur st.prev of
          Left err => throw err
          Right vs => emitList vs $> res
        Right ((o,bs),p2) => case plexBytes l o st bs of
          Left err       => throw err
          Right (st2,vs) => cons vs (go st2 p2)


module Text.ILex.FS

import Data.Linear.ELift1
import Data.Array.All
import Text.ILex.Internal.Runner
import Text.ILex.Runner1

import public FS
import public Text.ILex

import Derive.Prelude

%default total
%language ElabReflection

-- parameters (parser    : Parser StreamBounds e t a)
--            (start,end : StreamPos)
--
--   %inline
--   sappEOI : parser.state -> Either (StreamError t e) a
--   sappEOI state = parser.eoi (SB end end) state
--
--   %inline
--   bounds : StreamBounds
--   bounds = SB start end
--
--   ||| Tries to read the last token of an input stream and
--   ||| append it to the already accumulated list of tokens.
--   export
--   appLast :
--        (dfa   : DFA e t)
--     -> (cur   : Maybe (Tok e t))
--     -> (state : parser.state)
--     -> ByteString
--     -> Either (StreamError t e) a
--   appLast dfa Nothing  state bs = sappEOI state
--   appLast dfa (Just t) state bs =
--     case t of
--       Ignore    => sappEOI state
--       Const v   => parser.step (I v state bounds) >>= sappEOI
--       Txt f     => case f (toString bs) of
--         Left  x => Left $ B (Custom x) bounds
--         Right v => parser.step (I v state bounds) >>= sappEOI
--       Bytes f   => case f bs of
--         Left  x => Left $ B (Custom x) bounds
--         Right v => parser.step (I v state bounds) >>= sappEOI

export
streamParse :
     {auto lft : ELift1 q f}
  -> {auto has : Has (StreamError t e) es}
  -> Parser e t a
  -> Pull f (Origin,(n ** MBuffer q n)) es r
  -> Pull f a es r
-- streamParse prs = go (init Virtual prs)
--   where
--     go :
--          LexState e prs.state t
--       -> Pull f (Origin,(n ** MBuffer q n)) es r
--       -> Pull f a es r
--     go st p =
--       assert_total $ P.uncons p >>= \case
--         Left res      =>
--           case appLast prs st.pos st.end st.dfa st.tok st.state st.prev of
--             Left err => throw err
--             Right v  => emit v $> res
--         Right ((o,bs),p2) => do
--           (st2,m) <- pparseBytes1 prs o st bs
--           consMaybe m (go st2 p2)

module Text.ILex.FS

import Text.ILex.Internal.Runner

import public FS
import public Text.ILex

import Derive.Prelude

%default total
%language ElabReflection

record State s a where
  constructor S
  exprs : SnocList a
  stack : s

sstep : (p : Parser b e t a) -> Step b e (State p.state a) t
sstep p v (S se st) bs =
  case  p.step (I v st bs) of
    Right x  => Right (S se x)
    Left x   => case p.eoi bs st of
      Right x => S (se:<x) <$> p.step (I v p.init bs)
      _       => Left x

schunk : State s a -> (State s a, Maybe $ List a)
schunk st@(S [<] _) = (st, Nothing)
schunk (S sx stack) = (S [<] stack, Just $ sx <>> [])

export
streamParser :
     (p : Parser StreamBounds e t a)
  -> (isInit : p.state -> Bool)
  -> Parser StreamBounds e t (List a)
streamParser p isInit =
  P (S [<] p.init) (p.lex . stack) (\(I t s b) => sstep p t s b) schunk sEOI
  where
    sEOI : EOI StreamBounds e (State p.state a) t (List a)
    sEOI sb (S sx stack) =
      case isInit stack of
        True  => Right (sx <>> [])
        False => (\x => sx <>> [x]) <$> p.eoi sb stack

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


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

parameters (parser    : Parser StreamBounds e t a)
           (start,end : StreamPos)

  %inline
  sappEOI : parser.state -> Either (StreamError t e) a
  sappEOI state = parser.eoi (SB end end) state

  %inline
  bounds : StreamBounds
  bounds = SB start end

  ||| Tries to read the last token of an input stream and
  ||| append it to the already accumulated list of tokens.
  export
  appLast :
       (dfa   : DFA (Tok e t))
    -> (cur   : Maybe (Tok e t))
    -> (state : parser.state)
    -> ByteString
    -> Either (StreamError t e) a
  appLast dfa Nothing  state bs = sappEOI state
  appLast dfa (Just t) state bs =
    case t of
      Ignore    => sappEOI state
      Const v   => parser.step (I v state bounds) >>= sappEOI
      Txt f     => case f (toString bs) of
        Left  x => Left $ B (Custom x) bounds
        Right v => parser.step (I v state bounds) >>= sappEOI
      Bytes f   => case f bs of
        Left  x => Left $ B (Custom x) bounds
        Right v => parser.step (I v state bounds) >>= sappEOI

export
streamParse :
     {auto lft : ELift1 q f}
  -> {auto has : Has (StreamError t e) es}
  -> Parser StreamBounds e t a
  -> Pull f (Origin,(n ** MBuffer q n)) es r
  -> Pull f a es r
streamParse prs = go (init Virtual prs)
  where
    go :
         LexState e prs.state t
      -> Pull f (Origin,(n ** MBuffer q n)) es r
      -> Pull f a es r
    go st p =
      assert_total $ P.uncons p >>= \case
        Left res      =>
          case appLast prs st.pos st.end st.dfa st.tok st.state st.prev of
            Left err => throw err
            Right v  => emit v $> res
        Right ((o,bs),p2) => do
          (st2,m) <- pparseBytes1 prs o st bs
          consMaybe m (go st2 p2)

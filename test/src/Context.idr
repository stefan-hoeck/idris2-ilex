module Context

import Data.Buffer
import Data.Linear.Ref1
import Derive.Prelude
import Hedgehog
import Runner
import Syntax.T1
import Text.ILex

%default total
%hide Data.Linear.(.)
%language ElabReflection

public export
data Status = Dflt | Str

%runElab derive "Status" [Show,Eq]

||| Tokens of a context-sensitive lexer that uses
||| different lexemes for string literals.
public export
data Lit : Type where
  Num : Nat -> Lit
  SL  : String -> Lit

%runElab derive "Lit" [Show,Eq]

export
Interpolation Lit where interpolate = show

||| A record of mutable variables that can be used for
||| basic lexing tasks
public export
record ST q where
  constructor S
  line     : Ref q Nat
  col      : Ref q Nat
  bnds     : Ref q (SnocList Bounds)
  strs     : Ref q (SnocList String)
  vals     : Ref q (SnocList $ Bounded Lit)

export %inline
LC ST where
  line   = ST.line
  col    = ST.col
  bounds = ST.bnds

export %inline
LexST ST Lit where
  vals = ST.vals

export
init : F1 q (ST q)
init = T1.do
  l <- ref1 Z
  c <- ref1 Z
  b <- ref1 [<]
  s <- ref1 [<]
  v <- ref1 [<]
  pure (S l c b s v)

export
SLit, SStr : Index 2
SLit = 0
SStr = 1

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

closeStr : ST q -> F1 q (Index 2)
closeStr x = T1.do
  po <- popBounds x
  pe <- currentPos x
  s  <- getStr x.strs
  push1 (ST.vals x) SLit (B (SL s) $ po <+> atPos pe)

chars : RExp True
chars = plus $ dot && not '"' && not '\\'

lit1 : Lex1 q e 2 ST
lit1 =
  lex1
    [ E SLit $ dfa Err $ jsonSpaced SLit
        [ readTok decimal (Context.Num . cast)
        , copen '"' (const ST SStr)
        ]
    , E SStr $ dfa Err
        [ read chars $ push ST strs SStr
        , str #"\\"# $ push ST strs SStr #"\"#
        , str #"\""# $ push ST strs SStr #"""#
        , chr '"' closeStr
        ]
    ]

litErr : Arr32 2 (ST q -> ByteString -> F1 q (BoundedErr e))
litErr = errs [E SStr $ unclosedIfEOI "\"" []]

leoi : Index 2 -> ST q -> F1 q (Either (BoundedErr e) $ List (Bounded Lit))
leoi sk s =
  case sk == SLit of
    False => arrFail ST litErr sk s ""
    True  => replace1 s.vals [<] >>= pure . Right . (<>> [])

export
lit : P1 q (BoundedErr Void) 2 ST (List $ Bounded Lit)
lit = P SLit init lit1 (\x => (Nothing #)) litErr leoi

space : Nat -> Gen String
space n =  string (linear 0 5) (element [' ', '\t', '\r', '\t'])

genNum : Gen (Lit, String)
genNum = map (\n => (Num n, show n)) (nat $ linear 0 1000)

genStr : Gen (Lit, String)
genStr = choice [quote, esc, regular]
  where
    quote, esc, regular : Gen (Lit,String)
    quote = pure (SL "\"", #""\"""#)

    esc   = pure (SL "\\", #""\\""#)

    dropEsc : Char -> Char
    dropEsc '"'  = ' '
    dropEsc '\\' = ' '
    dropEsc c    = c

    regstr : Gen String
    regstr = string (linear 0 30) (map dropEsc printableAscii)

    regular = map (\s => (SL s, "\"\{s}\"")) regstr

prop_lexNum : Property
prop_lexNum =
  property $ do
    (l,s) <- forAll genNum
    Right [l] === lexNoBounds lit s

prop_lexStr : Property
prop_lexStr =
  property $ do
    (l,s) <- forAll genStr
    Right [l] === lexNoBounds lit s

prop_lexEmptyStr : Property
prop_lexEmptyStr =
  property1 $
    Right [SL ""] === lexNoBounds lit #""""#

prop_boundsNum : Property
prop_boundsNum =
  property1 $
        Right [B (Num 1234) $ BS (P 0 0) (P 0 4)]
    === lexBounds lit "1234"

prop_boundsStr : Property
prop_boundsStr =
  property1 $
        Right [B (SL "foo") $ BS (P 0 0) (P 0 5)]
    === lexBounds lit #""foo""#

prop_boundsQuote : Property
prop_boundsQuote =
  property1 $
        Right [B (SL #"""#) $ BS (P 0 0) (P 0 4)]
    === lexBounds lit #""\"""#

prop_boundsEsc : Property
prop_boundsEsc =
  property1 $ Right [B (SL #"\"#) $ BS (P 0 0) (P 0 4)]
    === lexBounds lit #""\\""#

prop_boundsEscErr : Property
prop_boundsEscErr =
  property1 $
        Left (PE Virtual (BS (P 0 3) (P 0 5)) (Just #""ab\D""#) (Expected [] #"\D"#))
    === lexBounds lit #""ab\D""#

prop_unclosedErr : Property
prop_unclosedErr =
  property1 $
        Left (PE Virtual (BS (P 0 0) (P 0 1)) (Just #""abc d"#) (Unclosed #"""#))
    === lexBounds lit #""abc d"#

export
props : Group
props =
  MkGroup "Text.ILex.Context"
    [ ("prop_lexNum", prop_lexNum)
    , ("prop_lexStr", prop_lexStr)
    , ("prop_lexEmptyStr", prop_lexEmptyStr)
    , ("prop_boundsNum", prop_boundsNum)
    , ("prop_boundsStr", prop_boundsStr)
    , ("prop_boundsQuote", prop_boundsQuote)
    , ("prop_boundsEsc", prop_boundsEsc)
    , ("prop_boundsEscErr", prop_boundsEscErr)
    , ("prop_unclosedErr", prop_unclosedErr)
    ]

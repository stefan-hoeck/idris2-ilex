module Context

import Data.Buffer
import Derive.Prelude
import Hedgehog
import Runner
import Text.ILex

%default total
%language ElabReflection

public export
data Status = Dflt | Str

%runElab derive "Status" [Show,Eq]

||| Tokens of a context-sensitive lexer that uses
||| different lexemes for string literals.
public export
data Lit : Type where
  Num : Nat -> Lit
  QO  : Lit -- opening quote
  QQ  : Lit -- closing quote
  SL  : String -> Lit
  E   : Lit

%runElab derive "Lit" [Show,Eq]

export
Interpolation Lit where interpolate = show

spaces : RExp True
spaces = plus (oneof [' ', '\n', '\r', '\t'])

strLit : DFA Void Status Lit
strLit =
  errEOI EOI $ dfa
    [ (chr,    txt' Str (SL . toString))
    , ("\\\\", Const Str  $ SL "\\")
    , ("\\\"", Const Str  $ SL "\"")
    , ('"',    Const Dflt QQ)
    ]
  where
    chr : RExp True
    chr = plus $ dot && not '"' && not '\\'

dfltLit : DFA Void Status Lit
dfltLit =
  setEOI E $ dfa
    [ (decimal, txt' Dflt (Num . cast . toString))
    , ('"', Const Str QO)
    , (spaces, Ignore Dflt)
    ]

export
lit : Lexer Void Status Lit
lit =
  L Dflt $ \case
    Dflt => dfltLit
    Str  => strLit

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
    regstr = string (linear 1 30) (map dropEsc printableAscii)

    regular = map (\s => (SL s, "\"\{s}\"")) regstr

prop_lexNum : Property
prop_lexNum =
  property $ do
    (l,s) <- forAll genNum
    Right [l,E] === lexNoBounds lit s

prop_lexStr : Property
prop_lexStr =
  property $ do
    (l,s) <- forAll genStr
    Right [QO,l,QQ,E] === lexNoBounds lit s

prop_lexEmptyStr : Property
prop_lexEmptyStr =
  property1 $
    Right [QO,QQ,E] === lexNoBounds lit #""""#

prop_boundsNum : Property
prop_boundsNum =
  property1 $
        Right
          [ B (Num 1234) $ BS 0 3
          , B E $ BS 4 4
          ]
    === lexString Virtual lit "1234"

prop_boundsStr : Property
prop_boundsStr =
  property1 $
        Right
          [ B QO         $ BS 0 0
          , B (SL "foo") $ BS 1 3
          , B QQ         $ BS 4 4
          , B E          $ BS 5 5
          ]
    === lexString Virtual lit #""foo""#

prop_boundsQuote : Property
prop_boundsQuote =
  property1 $
        Right
          [ B QO         $ BS 0 0
          , B (SL #"""#) $ BS 1 2
          , B QQ         $ BS 3 3
          , B E          $ BS 4 4
          ]
    === lexString Virtual lit #""\"""#

prop_boundsEsc : Property
prop_boundsEsc =
  property1 $
        Right
          [ B QO         $ BS 0 0
          , B (SL #"\"#) $ BS 1 2
          , B QQ         $ BS 3 3
          , B E          $ BS 4 4
          ]
    === lexString Virtual lit #""\\""#

prop_boundsEscErr : Property
prop_boundsEscErr =
  property1 $
        Left (PE Virtual (BS 4 4) #""ab\D""# (Byte 68))
    === lexString Virtual lit #""ab\D""#

prop_unclosedErr : Property
prop_unclosedErr =
  property1 $
        Left (PE Virtual (BS 6 6) #""abc d"# EOI)
    === lexString Virtual lit #""abc d"#

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

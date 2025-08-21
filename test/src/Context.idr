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
  QQ  : Lit -- closing quote
  SL  : String -> Lit
  SP  : SnocList String -> Lit

%runElab derive "Lit" [Show,Eq]

export
Interpolation Lit where interpolate = show

spaces : RExp True
spaces = plus (oneof [' ', '\n', '\r', '\t'])

strLit : DFA (Tok Void Lit)
strLit =
  dfa
    [ (chr,    txt SL)
    , ("\\\\", const $ SL "\\")
    , ("\\\"", const $ SL "\"")
    , ('"',    const QQ)
    ]
  where
    chr : RExp True
    chr = plus $ dot && not '"' && not '\\'

dfltLit : DFA (Tok Void Lit)
dfltLit =
  dfa
    [ (decimal, txt (Num . cast))
    , ('"', const $ SP [<])
    , (spaces, Ignore)
    ]

concatString : SnocList String -> Bounds -> Bounds -> Bounded Lit
concatString ss x y = B (SL $ fastConcat $ ss <>> []) (x<+>y)

lex : SnocList (Bounded Lit) -> DFA (Tok Void Lit)
lex (ss:< B (SP _) _) = strLit
lex _                 = dfltLit

step :
     Lit
  -> SnocList (Bounded Lit)
  -> Bounds
  -> ParseRes Bounds Void (SnocList $ Bounded Lit) Lit
step QQ       (ss:< B (SP sv) bs1) bs = Right (ss:< concatString sv bs1 bs)
step (SL s)   (ss:< B (SP sv) bs1) bs = Right (ss:< B (SP $ sv:<s) bs1)
step x@(SP _) ss                   bs = Right (ss:<B x bs)
step x        ss                   bs = Right (ss:<B x bs)

eoi : Bounds -> SnocList (Bounded Lit) -> Either (Bounded $ InnerError Lit Void) (List $ Bounded Lit)
eoi bs (sx:<B (SP _) _) = Left (B EOI bs)
eoi bs sx               = Right (sx<>>[])

export
lit : Lexer Bounds Void Lit
lit = P [<] lex (\(I v s b) => step v s b) (\s => (s,Nothing)) Context.eoi

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
        Right [B (Num 1234) $ BS 0 3]
    === parseString Virtual lit "1234"

prop_boundsStr : Property
prop_boundsStr =
  property1 $
        Right [B (SL "foo") $ BS 0 4]
    === parseString Virtual lit #""foo""#

prop_boundsQuote : Property
prop_boundsQuote =
  property1 $
        Right [B (SL #"""#) $ BS 0 3]
    === parseString Virtual lit #""\"""#

prop_boundsEsc : Property
prop_boundsEsc =
  property1 $ Right [B (SL #"\"#) $ BS 0 3]
    === parseString Virtual lit #""\\""#

prop_boundsEscErr : Property
prop_boundsEscErr =
  property1 $
        Left (PE Virtual (BS 4 4) #""ab\D""# (Byte 68))
    === parseString Virtual lit #""ab\D""#

prop_unclosedErr : Property
prop_unclosedErr =
  property1 $
        Left (PE Virtual (BS 6 6) #""abc d"# EOI)
    === parseString Virtual lit #""abc d"#

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

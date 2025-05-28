module Runner

import Derive.Prelude
import Text.ILex
import Hedgehog

%default total
%language ElabReflection

public export
data AorB : Type where
  MA : AorB
  A  : AorB
  B  : AorB
  E  : AorB -- end of input

%runElab derive "AorB" [Show,Eq]

export
Interpolation AorB where interpolate = show

spaces : RExp True
spaces = plus (oneof [' ', '\n', '\r', '\t'])

export
aOrB : Lexer Void AorB
aOrB =
  setEOI E $ lexer
    [ ('A' >> plus 'a', Const MA)
    , ('A', Const A)
    , (plus ('B' <|> 'b'), Const B)
    , (spaces, Ignore)
    ]

space : Nat -> Gen String
space n =  string (linear n 5) (element [' ', '\t', '\r', '\t'])

genSpace : Gen String
genSpace = space 1

genOptSpace : Gen String
genOptSpace = space 0

genA : Gen (AorB, String)
genA = map (\s => (A, "A" ++ s)) genOptSpace

genMA : Gen (AorB, String)
genMA = [| combine (string (linear 1 10) (pure 'a')) genOptSpace |]
  where
    combine : String -> String -> (AorB, String)
    combine bs space = (MA, "A" ++ bs ++ space)

genB : Gen (AorB, String)
genB = [| combine (string (linear 1 10) (element ['b', 'B'])) genSpace |]
  where
    combine : String -> String -> (AorB, String)
    combine bs space = (B, bs ++ space)


aOrBs : Gen (AorB, String)
aOrBs = choice [genA, genMA, genB]

lexNoBounds : Lexer e a -> String -> Either (ParseError a e) (List a)
lexNoBounds lex = map (map val) . lexString Virtual lex

prop_lexAorB : Property
prop_lexAorB =
  property $ do
    abs <- forAll $ list (linear 0 10) aOrBs
    let s := fastConcat $ map snd abs
    Right (map fst abs ++ [E]) === lexNoBounds aOrB s

export
props : Group
props =
  MkGroup "Text.ILex.Runner"
    [ ("prop_lexAorB", prop_lexAorB)
    ]

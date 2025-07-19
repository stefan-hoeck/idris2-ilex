module Runner

import Data.Buffer
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
  C  : AorB

%runElab derive "AorB" [Show,Eq]

export
Interpolation AorB where interpolate = show

spaces : RExp True
spaces = plus (oneof [' ', '\n', '\r', '\t'])

aOrB : Lexer b Void AorB
aOrB =
  lexer $ dfa
    [ ('A' >> plus 'a', const MA)
    , ('A', const A)
    , (plus ('B' <|> 'b'), const B)
    , ("Ccc", const C)
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

genC : Gen (AorB, String)
genC = pure (C, "Ccc")


aOrBs : Gen (AorB, String)
aOrBs = choice [genA, genMA, genB, genC]

export
lexNoBounds : Lexer Bounds e a -> String -> Either (ParseError a e) (List a)
lexNoBounds lex = map (map val) . parseString Virtual lex

export
lexBounds : Lexer Bounds e a -> String -> Either (ParseError a e) (List $ Bounded a)
lexBounds lex = parseString Virtual lex

prop_lexAorB : Property
prop_lexAorB =
  property $ do
    abs <- forAll $ list (linear 0 10) aOrBs
    let s := fastConcat $ map snd abs
    Right (map fst abs) === lexNoBounds aOrB s

prop_boundsAOnly : Property
prop_boundsAOnly =
  property1 $
        Right
          [ B A $ BS 0 0
          ]
    === lexBounds aOrB "A"

prop_boundsAsOnly : Property
prop_boundsAsOnly =
  property1 $
        Right
          [ B MA $ BS 1 4
          ]
    === lexBounds aOrB " Aaaa"

prop_boundsMany : Property
prop_boundsMany =
  property1 $
        Right
          [ B MA $ BS  1  4
          , B B  $ BS  8  9
          , B B  $ BS 11 14
          , B A  $ BS 16 16
          , B MA $ BS 19 21
          , B A  $ BS 22 22
          , B B  $ BS 23 23
          , B C  $ BS 24 26
          , B MA $ BS 29 30
          ]
    === lexBounds aOrB " Aaaa   Bb Bbbb A  AaaABCcc  Aa"

prop_boundsByteErr : Property
prop_boundsByteErr =
  property1 $
        Left (PE Virtual (BS 4 4) " AaaD" (Byte 68))
    === lexBounds aOrB " AaaD"

prop_boundsByteErr2 : Property
prop_boundsByteErr2 =
  property1 $
        Left (PE Virtual (BS 2 2) "CcD" (Byte 68))
    === lexBounds aOrB "CcD"

prop_boundsEoiErr : Property
prop_boundsEoiErr =
  property1 $
        Left (PE Virtual (BS 6 6) " AaaCc" EOI)
    === lexBounds aOrB " AaaCc"

export
props : Group
props =
  MkGroup "Text.ILex.Runner"
    [ ("prop_lexAorB", prop_lexAorB)
    , ("prop_boundsAOnly", prop_boundsAOnly)
    , ("prop_boundsAsOnly", prop_boundsAsOnly)
    , ("prop_boundsMany", prop_boundsMany)
    , ("prop_boundsByteErr", prop_boundsByteErr)
    , ("prop_boundsByteErr2", prop_boundsByteErr2)
    , ("prop_boundsEoiErr", prop_boundsEoiErr)
    ]

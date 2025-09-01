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

aOrB : L1 q Void AorB
aOrB =
  lexer $ jsonSpaced 0
    [ convTok0 ('A' >> plus 'a') (const MA)
    , ctok0 'A' A
    , convTok0 (plus ('B' <|> 'b')) (const B)
    , stok0 "Ccc" C
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
lexBounds : Parser1 (BoundedErr e) r s a -> String -> Either (ParseError e) a
lexBounds lex s = parseString lex Virtual s

export
lexNoBounds :
     Parser1 (BoundedErr e) r s (List $ Bounded a)
  -> String
  -> Either (ParseError e) (List a)
lexNoBounds lex = map (map val) . lexBounds lex

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
          [ B A $ BS (P 0 0) (P 0 0)
          ]
    === lexBounds aOrB "A"

prop_boundsAsOnly : Property
prop_boundsAsOnly =
  property1 $
        Right
          [ B MA $ BS (P 0 1) (P 0 4)
          ]
    === lexBounds aOrB " Aaaa"

prop_boundsMany : Property
prop_boundsMany =
  property1 $
        Right
          [ B MA $ BS (P 0  1) (P 0  4)
          , B B  $ BS (P 0  8) (P 0  9)
          , B B  $ BS (P 0 11) (P 0 14)
          , B A  $ BS (P 0 16) (P 0 16)
          , B MA $ BS (P 0 19) (P 0 21)
          , B A  $ BS (P 0 22) (P 0 22)
          , B B  $ BS (P 0 23) (P 0 23)
          , B C  $ BS (P 0 24) (P 0 26)
          , B MA $ BS (P 0 29) (P 0 30)
          ]
    === lexBounds aOrB " Aaaa   Bb Bbbb A  AaaABCcc  Aa"

prop_boundsByteErr : Property
prop_boundsByteErr =
  property1 $
        Left (PE Virtual (BS (P 0 4) (P 0 4)) (Just " AaaD") (Unexpected "D"))
    === lexBounds aOrB " AaaD"

prop_boundsByteErr2 : Property
prop_boundsByteErr2 =
  property1 $
        Left (PE Virtual (BS (P 0 0) (P 0 2)) (Just "CcD") (Unexpected "CcD"))
    === lexBounds aOrB "CcD"

prop_boundsEoiErr : Property
prop_boundsEoiErr =
  property1 $
        Left (PE Virtual (BS (P 0 4) (P 0 5)) (Just " AaaCc") (Unexpected "Cc"))
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

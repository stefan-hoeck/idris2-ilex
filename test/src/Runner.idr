module Runner

import Data.Buffer
import Derive.Prelude
import Text.ILex
import Hedgehog

%default total
%language ElabReflection

export
toErr : Position -> Position -> String -> InnerError e -> Either (ParseError e) a
toErr strt end s x = Left (PE Virtual (BS strt end) (BS strt end) (Just s) x)

public export
data Val : Type where
  MA  : Val
  A   : Val
  B   : Val
  C   : Val
  Foo : Val

%runElab derive "Val" [Show,Eq]

export
Interpolation Val where interpolate = show

val : L1 q Void 1 Val
val =
  lexer $ jsonSpaced (Ini {n = 1})
    [ convTok ('A' >> plus 'a') (const MA)
    , ctok 'A' A
    , convTok (plus $ charLike 'B') (const B)
    , ctok "Ccc" C
    , ctok (like "Foo") Foo
    ]

space : Nat -> Gen String
space n =  string (linear n 5) (element [' ', '\t', '\r', '\t'])

genSpace : Gen String
genSpace = space 1

genOptSpace : Gen String
genOptSpace = space 0

genA : Gen (Val, String)
genA = map (\s => (A, "A" ++ s)) genOptSpace

genMA : Gen (Val, String)
genMA = [| combine (string (linear 1 10) (pure 'a')) genOptSpace |]
  where
    combine : String -> String -> (Val, String)
    combine bs space = (MA, "A" ++ bs ++ space)

genB : Gen (Val, String)
genB = [| combine (string (linear 1 10) (element ['b', 'B'])) genSpace |]
  where
    combine : String -> String -> (Val, String)
    combine bs space = (B, bs ++ space)

genC : Gen (Val, String)
genC = pure (C, "Ccc")


vals : Gen (Val, String)
vals = choice [genA, genMA, genB, genC]

export
lexBounds : Parser1 (BoundedErr e) r s a -> String -> Either (ParseError e) a
lexBounds lex = parseString lex Virtual

export
lexBytes : Parser1 (BoundedErr e) r s a -> ByteString -> Either (ParseError e) a
lexBytes lex = parseBytes lex Virtual

export
lexNoBounds :
     Parser1 (BoundedErr e) r s (List $ Bounded a)
  -> String
  -> Either (ParseError e) (List a)
lexNoBounds lex = map (map val) . lexBounds lex

prop_lexAorB : Property
prop_lexAorB =
  property $ do
    abs <- forAll $ list (linear 0 10) vals
    let s := fastConcat $ map snd abs
    Right (map fst abs) === lexNoBounds val s

prop_boundsAOnly : Property
prop_boundsAOnly =
  property1 $
        Right
          [ B A $ BS (P 0 0) (P 0 1)
          ]
    === lexBounds val "A"

prop_boundsAsOnly : Property
prop_boundsAsOnly =
  property1 $
        Right
          [ B MA $ BS (P 0 1) (P 0 5)
          ]
    === lexBounds val " Aaaa"

prop_boundsFoo : Property
prop_boundsFoo =
  property1 $ do
    res === lexBounds val " foo"
    res === lexBounds val " fOo"
    res === lexBounds val " FOO"
    res === lexBounds val " Foo"
    res === lexBounds val " fOO"
  where
    res : Either a (List $ Bounded Val)
    res = Right [B Foo $ BS (P 0 1) (P 0 4)]

prop_boundsMany : Property
prop_boundsMany =
  property1 $
        Right
          [ B MA $ BS (P 0  1) (P 0  5)
          , B B  $ BS (P 0  8) (P 0 10)
          , B B  $ BS (P 0 11) (P 0 15)
          , B A  $ BS (P 0 16) (P 0 17)
          , B MA $ BS (P 0 19) (P 0 22)
          , B A  $ BS (P 0 22) (P 0 23)
          , B B  $ BS (P 0 23) (P 0 24)
          , B C  $ BS (P 0 24) (P 0 27)
          , B MA $ BS (P 0 29) (P 0 31)
          ]
    === lexBounds val " Aaaa   Bb bbBb A  AaaABCcc  Aa"

prop_boundsExpectedErr : Property
prop_boundsExpectedErr =
  property1 $
        toErr (P 0 4) (P 0 5) " AaaD" (Expected [] "D")
    === lexBounds val " AaaD"

prop_boundsExpectedErr2 : Property
prop_boundsExpectedErr2 =
  property1 $
        toErr (P 0 0) (P 0 3) "CcD" (Expected [] "CcD")
    === lexBounds val "CcD"

prop_boundsEoiErr : Property
prop_boundsEoiErr =
  property1 $
        toErr (P 0 4) (P 0 6) " AaaCc" (Expected [] "Cc")
    === lexBounds val " AaaCc"

prop_boundsByteErr : Property
prop_boundsByteErr =
  property1 $
        toErr (P 0 5) (P 0 6) " Aaaa\65533" (InvalidByte 0b1001_0011)
    === lexBytes val (" Aaaa" <+> pack [0b1001_0011])

prop_boundsByteErr2 : Property
prop_boundsByteErr2 =
  property1 $
        toErr (P 0 5) (P 0 6) " Aaaaä" (InvalidByte 0xc3)
    === lexBounds val " Aaaaä"

export
props : Group
props =
  MkGroup "Text.ILex.Runner"
    [ ("prop_lexAorB", prop_lexAorB)
    , ("prop_boundsAOnly", prop_boundsAOnly)
    , ("prop_boundsAsOnly", prop_boundsAsOnly)
    , ("prop_boundsFoo", prop_boundsFoo)
    , ("prop_boundsMany", prop_boundsMany)
    , ("prop_boundsExpectedErr", prop_boundsExpectedErr)
    , ("prop_boundsExpectedErr2", prop_boundsExpectedErr2)
    , ("prop_boundsEoiErr", prop_boundsEoiErr)
    , ("prop_boundsByteErr", prop_boundsByteErr)
    , ("prop_boundsByteErr2", prop_boundsByteErr2)
    ]

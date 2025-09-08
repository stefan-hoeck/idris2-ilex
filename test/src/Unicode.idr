module Unicode

import Derive.Prelude
import Hedgehog
import Hedgehog.Gen.Unicode as HU
import Runner
import Text.ILex
import Text.ILex.RExp.Unicode as U

%default total
%language ElabReflection

data Cat : Type where
  Cn : String -> Cat
  Lu : String -> Cat
  Ll : String -> Cat
  Lt : String -> Cat
  Lm : String -> Cat
  Lo : String -> Cat
  Mn : String -> Cat
  Me : String -> Cat
  Mc : String -> Cat
  Nd : String -> Cat
  Nl : String -> Cat
  No : String -> Cat
  Zs : String -> Cat
  Zl : String -> Cat
  Zp : String -> Cat
  Cc : String -> Cat
  Cf : String -> Cat
  Co : String -> Cat
  Pd : String -> Cat
  Ps : String -> Cat
  Pe : String -> Cat
  Pc : String -> Cat
  Po : String -> Cat
  Pi : String -> Cat
  Pf : String -> Cat
  Sm : String -> Cat
  Sc : String -> Cat
  Sk : String -> Cat
  So : String -> Cat

%runElab derive "Cat" [Show,Eq]

cat : L1 q Void 1 Cat
cat =
  lexer
    [ readTok U.unassigned Cn
    , readTok U.uppercaseLetter Lu
    , readTok U.lowercaseLetter Ll
    , readTok U.titlecaseLetter Lt
    , readTok U.modifierLetter Lm
    , readTok U.otherLetter Lo
    , readTok U.nonspacingMark Mn
    , readTok U.enclosingMark Me
    , readTok U.spacingMark Mc
    , readTok U.decimalNumber Nd
    , readTok U.letterNumber Nl
    , readTok U.otherNumber No
    , readTok U.spaceSeparator Zs
    , readTok U.lineSeparator Zl
    , readTok U.paragraphSeparator Zp
    , readTok U.control Cc
    , readTok U.format Cf
    , readTok U.privateUse Co
    , readTok U.dashPunctuation Pd
    , readTok U.openPunctuation Ps
    , readTok U.closePunctuation Pe
    , readTok U.connectorPunctuation Pc
    , readTok U.initialPunctuation Pi
    , readTok U.finalPunctuation Pf
    , readTok U.mathSymbol Sm
    , readTok U.currencySymbol Sc
    , readTok U.modifierSymbol Sk
    , readTok U.otherSymbol So
    ]

checkCat : (String -> Cat) -> Char -> PropertyT ()
checkCat f c =
 let s := Data.String.singleton c
  -- check for byte order mark, which is dropped when
  -- going from bytes to string
  in case cast c == 0xfeff of
    True  => lexNoBounds cat s === Right [f ""]
    False => lexNoBounds cat s === Right [f s]

prop_unassigned : Property
prop_unassigned =
  property $ forAll HU.unassigned >>= checkCat Cn

prop_uppercaseLetter : Property
prop_uppercaseLetter =
  property $ forAll HU.uppercaseLetter >>= checkCat Lu

prop_lowercaseLetter : Property
prop_lowercaseLetter =
  property $ forAll HU.lowercaseLetter >>= checkCat Ll

prop_titlecaseLetter : Property
prop_titlecaseLetter =
  property $ forAll HU.titlecaseLetter >>= checkCat Lt

prop_otherLetter : Property
prop_otherLetter =
  property $ forAll HU.otherLetter >>= checkCat Lo

prop_nonspacingMark : Property
prop_nonspacingMark =
  property $ forAll HU.nonspacingMark >>= checkCat Mn

prop_enclosingMark : Property
prop_enclosingMark =
  property $ forAll HU.enclosingMark >>= checkCat Me

prop_spacingMark : Property
prop_spacingMark =
  property $ forAll HU.spacingMark >>= checkCat Mc

prop_decimalNumber : Property
prop_decimalNumber =
  property $ forAll HU.decimalNumber >>= checkCat Nd

prop_letterNumber : Property
prop_letterNumber =
  property $ forAll HU.letterNumber >>= checkCat Nl

prop_otherNumber : Property
prop_otherNumber =
  property $ forAll HU.otherNumber >>= checkCat No

prop_spaceSeparator : Property
prop_spaceSeparator =
  property $ forAll HU.spaceSeparator >>= checkCat Zs

prop_lineSeparator : Property
prop_lineSeparator =
  property $ forAll HU.lineSeparator >>= checkCat Zl

prop_paragraphSeparator : Property
prop_paragraphSeparator =
  property $ forAll HU.paragraphSeparator >>= checkCat Zp

prop_control : Property
prop_control =
  property $ forAll HU.control >>= checkCat Cc

prop_format : Property
prop_format =
  property $ forAll HU.format >>= checkCat Cf

prop_privateUse : Property
prop_privateUse =
  property $ forAll HU.privateUse >>= checkCat Co

prop_dashPunctuation : Property
prop_dashPunctuation =
  property $ forAll HU.dashPunctuation >>= checkCat Pd

prop_openPunctuation : Property
prop_openPunctuation =
  property $ forAll HU.openPunctuation >>= checkCat Ps

prop_closePunctuation : Property
prop_closePunctuation =
  property $ forAll HU.closePunctuation >>= checkCat Pe

prop_connectorPunctuation : Property
prop_connectorPunctuation =
  property $ forAll HU.connectorPunctuation >>= checkCat Pc

prop_initialPunctuation : Property
prop_initialPunctuation =
  property $ forAll HU.initialPunctuation >>= checkCat Pi

prop_finalPunctuation : Property
prop_finalPunctuation =
  property $ forAll HU.finalPunctuation >>= checkCat Pf

prop_mathSymbol : Property
prop_mathSymbol =
  property $ forAll HU.mathSymbol >>= checkCat Sm

prop_currencySymbol : Property
prop_currencySymbol =
  property $ forAll HU.currencySymbol >>= checkCat Sc

prop_modifierSymbol : Property
prop_modifierSymbol =
  property $ forAll HU.modifierSymbol >>= checkCat Sk

prop_otherSymbol : Property
prop_otherSymbol =
  property $ forAll HU.otherSymbol >>= checkCat So

export
props : Group
props =
  MkGroup "Text.ILex.RExp.Unicode"
    [ ("prop_unassigned", prop_unassigned)
    , ("prop_uppercaseLetter", prop_uppercaseLetter)
    , ("prop_lowercaseLetter", prop_lowercaseLetter)
    , ("prop_titlecaseLetter", prop_titlecaseLetter)
    , ("prop_otherLetter", prop_otherLetter)
    , ("prop_nonspacingMark", prop_nonspacingMark)
    , ("prop_enclosingMark", prop_enclosingMark)
    , ("prop_spacingMark", prop_spacingMark)
    , ("prop_decimalNumber", prop_decimalNumber)
    , ("prop_letterNumber", prop_letterNumber)
    , ("prop_otherNumber", prop_otherNumber)
    , ("prop_spaceSeparator", prop_spaceSeparator)
    , ("prop_lineSeparator", prop_lineSeparator)
    , ("prop_paragraphSeparator", prop_paragraphSeparator)
    , ("prop_control", prop_control)
    , ("prop_format", prop_format)
    , ("prop_privateUse", prop_privateUse)
    , ("prop_dashPunctuation", prop_dashPunctuation)
    , ("prop_openPunctuation", prop_openPunctuation)
    , ("prop_closePunctuation", prop_closePunctuation)
    , ("prop_connectorPunctuation", prop_connectorPunctuation)
    , ("prop_initialPunctuation", prop_initialPunctuation)
    , ("prop_finalPunctuation", prop_finalPunctuation)
    , ("prop_mathSymbol", prop_mathSymbol)
    , ("prop_currencySymbol", prop_currencySymbol)
    , ("prop_modifierSymbol", prop_modifierSymbol)
    , ("prop_otherSymbol", prop_otherSymbol)
    ]

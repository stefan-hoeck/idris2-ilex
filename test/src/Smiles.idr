module Smiles

import Data.Finite
import Text.ILex
import Text.Smiles
import Text.Smiles.Lexer
import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
-- Chirality
--------------------------------------------------------------------------------

chiral : Expr False e is (is:<Chirality)
chiral =
      (str "@"   $> CW)
  <|> (str "@@"  $> CCW)
  <|> (str "TH1" $> TH1)
  <|> (str "TH2" $> TH2)
  <|> (str "AL1" $> AL1)
  <|> (str "AL2" $> AL2)
  <|> (str "SP1" $> SP1)
  <|> (str "SP2" $> SP2)
  <|> (str "SP3" $> SP3)
  <|> mpure Smiles.Types.None

--------------------------------------------------------------------------------
-- Elements
--------------------------------------------------------------------------------

toVal : Elem -> Expr False e is (is:<Elem)
toVal x = Expr.pure $ V (mtlift Elem) (VPlain (symbol x))

element : Expr True e is (is:<Elem)
element = choice (map elem values)
  where
    elem : Elem -> Expr True e is (is:<Elem)
    elem x =
      case unpack (symbol x) of
        c::cs => chars (c::cs) >>> toVal x
        []    => str "C" $> C -- this cannot happen

--------------------------------------------------------------------------------
-- Rings
--------------------------------------------------------------------------------

export
toRingNr : Integer -> RingNr
toRingNr x = fromMaybe 0 (refineRingNr $ cast x)

vdig : Val (Integer -> Integer -> RingNr)
vdig = mlift (\x,y => toRingNr (x * 10 + y))

ringNr : Expr True e is (is:<RingNr)
ringNr =
  (digit >>> marr toRingNr) <|>
  (chr_ '%' >>> zipWith [digit,digit] vdig)

--------------------------------------------------------------------------------
-- Bonds
--------------------------------------------------------------------------------

ToType SmilesBond where toType_ = mtlift SmilesBond

ToType Ring where toType_ = mtlift Ring

ToType SmilesToken where toType_ = mtlift SmilesToken

bond : Expr True e is (is:<SmilesBond)
bond =
      (chr_ '-'  $> Sngl)
  <|> (chr_ ':'  $> Arom)
  <|> (chr_ '='  $> Dbl)
  <|> (chr_ '#'  $> Trpl)
  <|> (chr_ '$'  $> Quad)
  <|> (chr_ '/'  $> FW)
  <|> (chr_ '\\' $> BW)

vring : Val (RingNr -> Maybe SmilesBond -> Ring)
vring = mlift R

ring : Expr True e is (is:<Ring)
ring = zipWith [ringNr, opt bond] vring

--------------------------------------------------------------------------------
-- Subset Atoms
--------------------------------------------------------------------------------

subset : Expr True e is (is:<SmilesAtom)
subset =
      (chr_ 'C' $> SubsetAtom C False)
  <|> (chr_ 'c' $> SubsetAtom C True)
  <|> (chr_ 'N' $> SubsetAtom N False)
  <|> (chr_ 'n' $> SubsetAtom N True)
  <|> (chr_ 'O' $> SubsetAtom O False)
  <|> (chr_ 'o' $> SubsetAtom O True)
  <|> (chr_ 'S' $> SubsetAtom S False)
  <|> (chr_ 's' $> SubsetAtom S True)
  <|> (chr_ 'P' $> SubsetAtom P False)
  <|> (chr_ 'p' $> SubsetAtom P True)
  <|> (chr_ 'B' $> SubsetAtom B False)
  <|> (chr_ 'b' $> SubsetAtom B True)
  <|> (chr_ 'F' $> SubsetAtom F False)
  <|> (str "Cl" $> SubsetAtom Cl False)
  <|> (str "Br" $> SubsetAtom Br False)
  <|> (chr_ 'I' $> SubsetAtom I False)

--------------------------------------------------------------------------------
-- Bracket Atoms
--------------------------------------------------------------------------------

toAromIso : Val (Maybe MassNr -> Elem -> AromIsotope)
toAromIso = mlift (\mn,e => MkAI e mn False)

-- TODO: Restrict this to the valid range of mass numbers
massNr : Expr False e is (is:<Maybe MassNr)
massNr = (decimal >>> marr (\x => refineMassNr (cast x))) <|> mpure Nothing

-- TODO: Add support for aromatic atoms
iso : Expr True e is (is:<AromIsotope)
iso = zipWith [massNr,element] toAromIso

-- TODO: Support larger charges
charge : Expr False e is (is:<Charge)
charge =
      (chr_ '+'  $> Charge.fromInteger 1)
  <|> (str  "++" $> Charge.fromInteger 2)
  <|> (chr_ '-'  $> Charge.fromInteger (-1))
  <|> (str  "--" $> Charge.fromInteger (-2))
  <|> mpure (Charge.fromInteger 0)

vhcount : Val (Integer -> HCount)
vhcount = mlift (\x => fromMaybe 0 (refineHCount (cast x)))

hcount : Expr False e is (is:<HCount)
hcount =
      (chr_ 'H'  $> HCount.fromInteger 1)
  <|> (chr_ 'H' >>> posdigit >>> arr vhcount)
  <|> mpure (HCount.fromInteger 0)

vbrckt : Val (AromIsotope -> Chirality -> HCount -> Charge -> SmilesAtom)
vbrckt = mlift bracket

brckt : Expr True e is (is:<SmilesAtom)
brckt = chr_ '[' >>> zipWith [iso, chiral, hcount, charge] vbrckt >>> chr_ ']'

--------------------------------------------------------------------------------
-- Tokens
--------------------------------------------------------------------------------

vta : Val (SmilesAtom -> SnocList Ring -> SmilesToken)
vta = mlift TA

token : Expr True e is (is:<SmilesToken)
token =
      (chr_ '(' $> PO)
  <|> (chr_ ')' $> PC)
  <|> (chr_ '.' $> Dot)
  <|> (bond >>> marr Lexer.TB)
  <|> (zipWith [subset <|> brckt, many ring] vta)

tokens : Expr False Util.LexErr [<] [<SnocList $ SmilesToken]
tokens = many (token) >>> eoi

covering
main : IO ()
main = do
  putStrLn
    """
    module SmilesLexer

    import Smiles
    import Text.ILex.Util
    import Text.Smiles
    import Text.Smiles.Lexer

    %hide Text.Smiles.Lexer.LexErr
    %hide Data.List.Suffix.Result0.Unexpected
    %hide Data.List.Suffix.Result0.EOI
    %hide Text.ParseError.EOI
    """
  putStrLn (generate "smiles" tokens)

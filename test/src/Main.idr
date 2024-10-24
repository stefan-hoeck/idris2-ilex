module Main

import Data.SnocList
import Lexer
import Package
import Smiles
import SmilesLexer
import Text.Smiles.Lexer
import PackageLexer
import Text.ILex.Util

toLst : Either a (SnocList b) -> List b
toLst = either (const []) (<>> [])

pkg : String

main : IO ()
main = do
  putStrLn "SMILES Tokens:"
  traverse_ printLn (toLst $ smiles "[13CH2+]c1ccccc1CC#N")

  putStrLn "\nNatural Numbers:"
  traverse_ printLn (toLst $ lexNat "1,10,0b1100,0xffaa,0,100")

  putStrLn "\n.ipkg Tokens:"
  traverse_ printLn (toLst $ lexTok pkg)

pkg =
  """
  package ilex
  version = 0.1.0
  authors = "stefan-hoeck"
  brief   = "Generating fast Lexers from an Idris2 DSL"
  langversion >= 0.7
  depends = elab-util
          , elab-pretty

  sourcedir = "src"

  modules = Text.ILex
          , Text.ILex.Args
          , Text.ILex.Codegen
          , Text.ILex.DFA
          , Text.ILex.Expr
          , Text.ILex.Set
          , Text.ILex.Util
          , Text.ILex.Val
  """

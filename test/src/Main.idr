module Main

import Data.SnocList
import Lexer
import Package
import PackageLexer
import Text.ILex.Util

pkg : String

main : IO ()
main = do
  printLn (lexNat "1,10,0b1100,0xffaa,0,100")
  printLn (lexTok pkg)

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

module Main

import Data.SnocList
import Lexer
import Package
import PackageLexer
import Text.ILex.Util

main : IO ()
main = do
  printLn (lexNat "1,10,0b1100,0xffaa,0,100")
  printLn (lexTok "Text.ILex.Expr == = >=  122>=13.4 -- a comment")

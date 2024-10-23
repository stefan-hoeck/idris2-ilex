module Main

import Data.SnocList
import Text.ILex.Util
import Lexer

main : IO ()
main = printLn (lexNat "1,10,0b1100,0xffaa,0,100")

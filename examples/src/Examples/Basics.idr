module Examples.Basics

import Data.ByteString
import Data.List
import Examples.Types
import Language.Reflection
import Text.ILex.Debug
import Text.ILex.RExp

%default total

spaces : RExp True
spaces = plus (oneof [' ', '\n', '\r', '\t'])

export
aOrB : TokenMap AorB
aOrB =
  [ (plus ('A' <|> 'a'), const A)
  , (plus ('B' <|> 'b'), const B)
  , (spaces, Ignore)
  ]

export
expr : TokenMap Expr
expr =
  [ (natural, bytes toNat)
  , ('+', const Plus)
  , ('*', const Mult)
  , ('(', const PO)
  , (')', const PC)
  , (spaces, Ignore)
  ]

identifier : RExp True
identifier = plus $ alphaNum <|> '_'

export
ident : TokenMap Ident
ident =
  [ ("else" >> opt identifier, const Else)
  , (identifier, bytes Id)
  ]

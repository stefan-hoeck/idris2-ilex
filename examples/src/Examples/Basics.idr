module Examples.Basics

import Data.ByteString
import Data.List
import Examples.Types
import Language.Reflection

import Text.ILex.Codegen
import Text.ILex.Debug
import Text.ILex.RExp

%default total

spaces : RExp True
spaces = plus (oneof [' ', '\n', '\r', '\t'])

export
ToType AorB where
  toType_ = TO "AorB"

export
aOrB : TokenMap (Val $ Conv AorB)
aOrB =
  [ (plus ('A' <|> 'a'), const A)
  , (plus ('B' <|> 'b'), const B)
  , (spaces, ignore)
  ]

export
ToType Expr where
  toType_ = TO "Expr"

export
expr : TokenMap (Val $ Conv Expr)
expr =
  [ (natural, bytes toNat)
  , ('+', const Plus)
  , ('*', const Mult)
  , ('(', const PO)
  , (')', const PC)
  , (spaces, ignore)
  ]

identifier : RExp True
identifier = plus $ alphaNum <|> '_'

export
ToType Ident where
  toType_ = TO "Ident"

export
ident : TokenMap (Val $ Conv Ident)
ident =
  [ ("else", const Else)
  , (identifier, bytes (Id . toString))
  , (spaces, ignore)
  ]

export
ToType JSON where
  toType_ = TO "JSON"

jstr : RExp True
jstr = '"' >> star (chr <|> esc <|> uni) >> '"'
  where
    chr : RExp True
    chr = dot && not '"' && not '\\'

    esc : RExp True
    esc = '\\' >> oneof ['\\','n','f','b','r','t','/','"']

    uni : RExp True
    uni = "\\u" >> hexdigit >> hexdigit >> hexdigit >> hexdigit

export
json : TokenMap (Val $ Conv JSON)
json =
  [ ("null",  const Null)
  , ("true",  const (JBool True))
  , ("false", const (JBool False))
  , ('{',     const JPO)
  , ('}',     const JPC)
  , ('[',     const JBO)
  , (']',     const JBC)
  , (',',     const JComma)
  , (':',     const JColon)
  , (jstr,    bytes (JStr . toString))
  , (decimal, bytes (JInt . decNat))
  , ('-' >> decimal, bytes (JInt . negate . decNat))
  , (spaces,  ignore)
  ]

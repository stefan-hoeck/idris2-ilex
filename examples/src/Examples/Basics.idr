module Examples.Basics

import Examples.Types

import Text.ILex.Runner
import Text.ILex.Debug

%default total

spaces : RExp True
spaces = plus (oneof [' ', '\n', '\r', '\t'])

export
aOrB : Lexer AorB
aOrB =
  lexer
    [ (plus ('A' <|> 'a'), Const A)
    , (plus ('B' <|> 'b'), Const B)
    , (spaces, Ignore)
    ]

export
expr : TokenMap (Conv Expr)
expr =
  [ (natural, Txt toNat)
  , ('+', Const Plus)
  , ('*', Const Mult)
  , ('(', Const PO)
  , (')', Const PC)
  , (spaces, Ignore)
  ]

identifier : RExp True
identifier = plus $ alphaNum <|> '_'

export
ident : Lexer Ident
ident =
  lexer
    [ ("else", Const Else)
    , (identifier, Txt (Id . toString))
    , (spaces, Ignore)
    ]

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
json : Lexer JSON
json =
  lexer
    [ ("null",  Const Null)
    , ("true",  Const (JBool True))
    , ("false", Const (JBool False))
    , ('{',     Const JPO)
    , ('}',     Const JPC)
    , ('[',     Const JBO)
    , (']',     Const JBC)
    , (',',     Const JComma)
    , (':',     Const JColon)
    , (jstr,    Txt (JStr . toString))
    , (decimal, Txt (JInt . decNat))
    , ('-' >> decimal, Txt (JInt . negate . decNat))
    , (spaces,  Ignore)
    ]

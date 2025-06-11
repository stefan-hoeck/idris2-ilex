module Examples.Basics

import Examples.Types

import Text.ILex.Runner
import Text.ILex.Debug

%default total

spaces : RExp True
spaces = plus (oneof [' ', '\n', '\r', '\t'])

export
aOrB : Lexer Void AorB
aOrB =
  setEOI E $ lexer
    [ (plus ('A' <|> 'a'), Const A)
    , (plus ('B' <|> 'b'), Const B)
    , (spaces, Ignore)
    ]

export
expr : TokenMap (Conv Void Expr)
expr =
  [ (natural, txt toNat)
  , ('+', Const Plus)
  , ('*', Const Mult)
  , ('(', Const PO)
  , (')', Const PC)
  , (spaces, Ignore)
  ]

identifier : RExp True
identifier = plus $ alphaNum <|> '_'

export
ident : Lexer Void Ident
ident =
  setEOI IE $ lexer
    [ ("else", Const Else)
    , (identifier, txt (Id . toString))
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

double : RExp True
double =
  let frac  = '.' >> plus digit
      exp   = oneof ['e','E'] >> opt (oneof ['+','-']) >> plus digit
   in opt '-' >> decimal >> opt frac >> opt exp

export
json : Lexer Void JSON
json =
  setEOI JEOI $ lexer
    [ ("null",  Const Null)
    , ("true",  Const (JBool True))
    , ("false", Const (JBool False))
    , ('{',     Const JPO)
    , ('}',     Const JPC)
    , ('[',     Const JBO)
    , (']',     Const JBC)
    , (',',     Const JComma)
    , (':',     Const JColon)
    , (jstr,    txt (JStr . toString))
    , (decimal, txt (JInt . decNat))
    , ('-' >> decimal, txt (JInt . negate . decNat))
    , (double,  txt (JNum . cast . toString))
    , (spaces,  Ignore)
    ]

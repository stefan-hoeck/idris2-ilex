module Examples.Basics

import Examples.Types

import Text.ILex.Runner
import Text.ILex.Debug

%default total

spaces : RExp True
spaces = plus (oneof [' ', '\n', '\r', '\t'])

export
aOrB : Lexer Void () AorB
aOrB =
  lexer $ setEOI E $ dfa
    [ (plus ('A' <|> 'a'), const A)
    , (plus ('B' <|> 'b'), const B)
    , (spaces, ignore)
    ]

export
expr : TokenMap (Conv Void () Expr)
expr =
  [ (natural, txt toNat)
  , ('+', const Plus)
  , ('*', const Mult)
  , ('(', const PO)
  , (')', const PC)
  , (spaces, ignore)
  ]

identifier : RExp True
identifier = plus $ alphaNum <|> '_'

export
ident : Lexer Void () Ident
ident =
  lexer $ setEOI IE $ dfa
    [ ("else", const Else)
    , (identifier, txt (Id . toString))
    , (spaces, ignore)
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
json : Lexer Void () JSON
json =
  lexer $ setEOI JEOI $ dfa
    [ ("null",  const Null)
    , ("true",  const (JBool True))
    , ("false", const (JBool False))
    , ('{',     const JPO)
    , ('}',     const JPC)
    , ('[',     const JBO)
    , (']',     const JBC)
    , (',',     const JComma)
    , (':',     const JColon)
    , (jstr,    txt (JStr . toString))
    , (decimal, txt (JInt . decNat))
    , ('-' >> decimal, txt (JInt . negate . decNat))
    , (double,  txt (JNum . cast . toString))
    , (spaces,  ignore)
    ]

module Examples.Basics

import Examples.Types

import Text.ILex

%default total
%hide Data.Linear.(.)

export
aOrB : L1 q Void AorB
aOrB =
  lexer {r = 1} $ jsonSpaced
    [ tok (plus ('A' <|> 'a')) A
    , tok (plus ('B' <|> 'b')) B
    ]

identifier : RExp True
identifier = plus $ alphaNum <|> '_'

export
ident : L1 q Void Ident
ident =
  lexer {r = 1} $ jsonSpaced
    [ tok "else" Else
    , stringTok identifier Id
    ]

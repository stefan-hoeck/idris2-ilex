module Examples.Basics

import Examples.Types

import Text.ILex

%default total
%hide Data.Linear.(.)

export
aOrB : L1 q Void 1 AorB
aOrB =
  lexer $ jsonSpaced (Ini {n = 1})
    [ convTok (plus ('A' <|> 'a')) (const A)
    , convTok (plus ('B' <|> 'b')) (const B)
    ]

-- export
-- exprDFA : DFA (Tok Void TExpr)
-- exprDFA =
--   dfa
--     [ (natural, bytes (TLit . decimal))
--     , ('+', const $ TOp P)
--     , ('-', const $ TOp S)
--     , ('*', const $ TOp M)
--     , ('^', const $ TOp X)
--     , ('(', const PO)
--     , (')', const PC)
--     , (spaces, Ignore)
--     ]
--
identifier : RExp True
identifier = plus $ alphaNum <|> '_'

export
ident : L1 q Void 1 Ident
ident =
  lexer $ jsonSpaced (Ini {n = 1})
    [ ctok "else" Else
    , readTok identifier Id
    ]

module Examples.Basics

import Examples.Types

import Text.ILex

%default total
%hide Data.Linear.(.)

spaces : RExp True
spaces = plus (oneof [' ', '\n', '\r', '\t'])

export
aOrB : Lexer b Void AorB
aOrB =
  lexer $ dfa
    [ (plus ('A' <|> 'a'), const A)
    , (plus ('B' <|> 'b'), const B)
    , (spaces, Ignore)
    ]

export
exprDFA : DFA Void TExpr
exprDFA =
  dfa
    [ (natural, txt toNat)
    , ('+', const $ TOp P)
    , ('-', const $ TOp S)
    , ('*', const $ TOp M)
    , ('^', const $ TOp X)
    , ('(', const PO)
    , (')', const PC)
    , (spaces, Ignore)
    ]

identifier : RExp True
identifier = plus $ alphaNum <|> '_'

export
ident : Lexer b Void Ident
ident =
  lexer $ dfa
    [ ("else", const Else)
    , (identifier, txt (Id . toString))
    , (spaces, Ignore)
    ]

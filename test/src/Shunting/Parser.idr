module Shunting.Parser

import public Shunting.Term
import Text.ILex
import Text.ILex.State.Derive
import Text.ILex.State.Streaming

%default total
%language ElabReflection

%runElab deriveParserState "Lexers" "Lexer" ["TERM","INFIX","ERR"]

data STACK : Type where
  Top   : STACK
  Seq   : STACK -> Skot Syntax Op -> STACK
  SeqT  : STACK -> Skot Syntax Op -> Syntax -> STACK
  Open  : STACK -> STACK

0 ST : Type -> Type
ST = State Void STACK Syntax Lexers

parameters {auto sk : ST q}

  putTerm : Syntax -> STACK -> F1 q Lexer
  putTerm trm (Seq p sx) = putStackAs (SeqT p sx trm) INFIX
  putTerm trm p          = putStackAs (SeqT p [<] trm) INFIX

  %inline
  onTerm : Syntax -> F1 q Lexer
  onTerm = withStack . putTerm

  onInfix : (o : Op) -> (0 p : IsInfix (cast o)) => F1 q Lexer
  onInfix o =
    withStack $ \case
      SeqT p st t => putStackAs (Seq p $ st:<tinf t o) TERM
      _           => failUnexpected [] ERR

  onPrefix : (o : Op) -> (0 p : IsPrefix (cast o)) => F1 q Lexer
  onPrefix o =
    withStack $ \case
      Seq p st => putStackAs (Seq p $ st:<tpre o) TERM
      p        => putStackAs (Seq p [<tpre o]) TERM

  onClose : F1 q Lexer
  onClose =
    withStack $ \case
      SeqT (Open p) st s => putTerm (sseq st s) p
      _                  => failUnexpected [] ERR

  onSemi : F1 q Lexer
  onSemi =
    withStack $ \case
      SeqT Top st t => pushValue (sseq st t) Top TERM
      _             => failUnexpected [] ERR

linecomment : RExp True
linecomment = "--" >> star dot

spaced : Lexer -> Steps q Lexers ST -> Entry Lexers (DFA q Lexers ST)
spaced x ss = E x $ dfa $ jsonSpaced $ ignore linecomment :: ss

ptrans : Lex1 q Lexers ST
ptrans =
  lex1
    [ spaced TERM
        [ bytes decimal (onTerm . SNat . cast . decimal)
        , step "true" (onTerm $ SBool True)
        , step "false" (onTerm $ SBool False)
        , step "-" (onPrefix NEG)
        , step "~" (onPrefix NOT)
        , opn '(' $ modStackAs ST Open TERM
        ]
    , spaced INFIX
        [ close ')' onClose
        , step ';' onSemi
        , step "+"  $ onInfix PLUS
        , step "-"  $ onInfix MINUS
        , step "*"  $ onInfix TIMES
        , step "^"  $ onInfix POW
        , step "==" $ onInfix EQ
        , step ">"  $ onInfix GT
        , step "<"  $ onInfix LT
        , step ">=" $ onInfix GTE
        , step "<=" $ onInfix LTE
        , step "&&" $ onInfix AND
        , step "||" $ onInfix OR
        ]
    ]

perr : Arr32 Lexers (ST q -> F1 q $ BBErr Void)
perr = errs []

peoi : Lexer -> ST q -> F1 q (Either (BBErr Void) $ List Syntax)
peoi st sk t =
 let Top # t := getStack t | _ # t => arrFail ST perr st sk t
  in values sk t

export
terms : P1 q (BBErr Void) (List Syntax)
terms = P TERM (init TERM Top) ptrans valuesChunk perr peoi

convert : Syntax -> String
convert = either show interpolate . desugar

test : String -> IO ()
test s =
  case parseString terms Virtual s of
    Left x   => putStrLn "\{x}"
    Right ts => traverse_ (putStrLn . convert) ts

module Shunting.Parser

import public Shunting.Term
import Text.ILex
import Text.ILex.State.Derive
import Text.ILex.State.Streaming
import Syntax.T1

%default total
%language ElabReflection

%runElab deriveParserState "Lexers" "Lexer" ["TERM","INFIX","ERR"]


data STACK : Type where
  Top   : STACK
  Seq   : STACK -> Skot Syntax POp IOp -> STACK
  SeqT  : STACK -> Skot Syntax POp IOp -> Syntax -> STACK
  Open  : STACK -> STACK

0 ST : Type -> Type
ST = State (ShuntingErr IOp) STACK Syntax Lexers

parameters {auto sk : ST q}

  putTerm : Syntax -> STACK -> F1 q Lexer
  putTerm trm (Seq p sx) = putStackAs (SeqT p sx trm) INFIX
  putTerm trm p          = putStackAs (SeqT p [<] trm) INFIX

  %inline
  onTerm : Syntax -> F1 q Lexer
  onTerm = withStack . putTerm

  onInfix : IOp -> Nat -> Assoc -> F1 q Lexer
  onInfix o n a =
    bounds >>= \b => withStack $ \case
      SeqT p st t => putStackAs (Seq p $ st:<TInf t (B o b) n a) TERM
      _           => failUnexpected [] ERR

  onPrefix : POp -> Nat -> F1 q Lexer
  onPrefix o n = T1.do
    b <- bounds
    withStack $ \case
      Seq p st => putStackAs (Seq p $ st:<TPre (B o b) n) TERM
      p        => putStackAs (Seq p [<TPre (B o b) n]) TERM

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
        , step "-" (onPrefix NEG 11)
        , step "~" (onPrefix NOT 11)
        , opn '(' $ modStackAs ST Open TERM
        ]
    , spaced INFIX
        [ close ')' onClose
        , step ';' onSemi
        , step "+"  $ onInfix PLUS 8 InfixL
        , step "-"  $ onInfix MINUS 8 InfixL
        , step "*"  $ onInfix TIMES 9 InfixL
        , step "^"  $ onInfix POW 10 InfixR
        , step "==" $ onInfix EQ 6 None
        , step ">"  $ onInfix GT 6 None
        , step "<"  $ onInfix LT 6 None
        , step ">=" $ onInfix GTE 6 None
        , step "<=" $ onInfix LTE 6 None
        , step "&&" $ onInfix AND 5 InfixR
        , step "||" $ onInfix OR 4 InfixR
        ]
    ]

perr : Arr32 Lexers (ST q -> F1 q TErr)
perr = errs []

peoi : Lexer -> ST q -> F1 q (Either TErr $ List Syntax)
peoi st sk t =
 let Top # t := getStack t | _ # t => arrFail ST perr st sk t
  in values sk t

export
terms : P1 q TErr (List Syntax)
terms = P TERM (init TERM Top) ptrans valuesChunk perr peoi

export
testTerm : String -> Either String (List Term)
testTerm s =
  mapFst (interpolate . toParseError Virtual s) $
    runString terms s >>= traverse desugar

runTest : String -> IO ()
runTest = either putStrLn (traverse_ $ putStrLn . interpolate) . testTerm

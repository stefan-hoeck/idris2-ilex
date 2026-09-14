module Shunting.Parser

import public Shunting.Term
import Text.ILex
import Text.ILex.State.Derive
import Text.ILex.State.Streaming

%default total
%language ElabReflection

%runElab deriveParserState "Lexers" "Lexer"
  ["TERM","INFIX","ERR"]

data STACK : Type where
  Top   : STACK
  Seq   : STACK -> SnocList (Skot Syntax Op) -> STACK
  SeqT  : STACK -> SnocList (Skot Syntax Op) -> Syntax -> STACK
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

  onPrefix : (o : Op) -> (0 p : IsPrefix (cast o)) => F1 q Lexer

--   onClose : F1 q Lexer
--   onClose =
--     getStack >>= \case
--       Seq (Open p) sx s => putTerm (seq sx s) p
--       _                 => failUnexpected [] ERR
--
--   onSemi : F1 q Lexer
--   onSemi =
--     getStack >>= \case
--       Seq (Def (Top sd) n) x s => putStackAs (Top $ sd:<Defn n (seq x s)) TOP
--       _                        => failUnexpected [] ERR
--
-- identchar : RExp True
-- identchar = alphaNum <|> '_' <|> '\''
--
-- ident : RExp True
-- ident = alpha >> star identchar
--
-- linecomment : RExp True
-- linecomment = "--" >> star dot
--
-- spaced : Lexer -> Steps q Lexers SK -> Entry Lexers (DFA q Lexers SK)
-- spaced x ss = E x $ dfa $ jsonSpaced [ignore linecomment]
--
-- ptrans : Lex1 q Lexers SK
-- ptrans =
--   lex1
--     [ spaced TERM
--         [ bytes integer (onTerm . SInt . integer)
--         , step "true" (onTerm $ SBool True)
--         , step "false" (onTerm $ SBool False)
--         , opn '(' $ modStackAs SK Open TERM
--         , string ident (onTerm . SDef)
--         ]
--     , spaced OP
--         [ close ')' onClose
--         , step ';' onSemi
--         , step "+"  $ onOp PLUS
--         , step "-"  $ onOp MINUS
--         , step "*"  $ onOp TIMES
--         , step "==" $ onOp EQ
--         , step ">"  $ onOp GT
--         , step "<"  $ onOp LT
--         , step ">=" $ onOp GTE
--         , step "<=" $ onOp LTE
--         , step "&&" $ onOp AND
--         , step "||" $ onOp OR
--         ]
--       , spaced TOP
--           [ step' "import" IMPORT
--           , string ident $ \s => modStackAs SK (`Def` s) EQUAL
--           ]
--       , spaced IMPORT [string ident onImport]
--       , spaced EQUAL [step' '=' TERM]
--     ]
--
-- perr : Arr32 Lexers (SK q -> F1 q $ BBErr Void)
-- perr = errs []
--
-- peoi : Lexer -> SK q -> F1 q (Either (BBErr Void) $ List Decl)
-- peoi st sk t =
--  let Top sd # t := getStack t | _ # t => arrFail SK perr st sk t
--   in Right (sd <>> []) # t
--
-- export
-- decls : P1 q (BBErr Void) (List Decl)
-- decls = P TOP (init $ Top [<]) ptrans (\x => (Nothing #)) perr peoi

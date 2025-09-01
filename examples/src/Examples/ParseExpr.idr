module Examples.ParseExpr

import Examples.Types
import Examples.Basics
import Text.ILex

%default total

-- public export
-- data Tpe = E | O
--
-- -- OP    := + | - | * | ^ (in order of binding priority)
-- -- NUM   := 0 | [1-9][0-9]*
-- -- EXPR  := NUM | (EXPR) | EXPR OP EXPRS
-- -- EXPRS := EXPR | EXPR OP EXPRS
-- --
-- -- OP and NUM, being only based on regexes, come from the lexer
--
-- -- EXPRS can be modeled as a `SnocList` of `(Expr,Op)` pairs followed
-- --       by one final expression.
--
-- -- Nesting of parenthesis can be modeled by giving the expresion
-- -- currently being formed a (partially complete) parent expression
-- -- If a paren is opened, the current partial expression becomes
-- -- the new expression's parent. If a parent is closed, the current
-- -- sequence of expression-operator pairs is merged into a single
-- -- expression (see the `Text.ILex.Util.mergeL` utility) and
-- -- appended to its parent expression.
-- public export
-- data PExpr : (b : Type) -> (tpe : Tpe) -> Type where
--   Ini : PExpr b O
--   PO  : PExpr b O -> b -> SnocList (Expr,Op) -> PExpr b O
--   PE  : PExpr b O -> b -> SnocList (Expr,Op) -> Expr -> PExpr b E
--
-- export %inline
-- init : b -> PExpr b O
-- init bs = PO Ini bs [<]
--
-- export
-- exprStep : EStep b Void (PExpr b) TExpr
-- exprStep (TLit x) (PO p bs sy)   _   = right $ PE p bs sy (Lit x)
-- exprStep (TOp o)  (PE p bs sy x) _   = right $ PO p bs $ sy :< (x,o)
-- exprStep PO       p@(PO {})      bs2 = right $ PO p bs2 [<]
-- exprStep PC       (PE p _ sy x)  bs2 =
--   case p of
--     PO p bs sx => right $ PE p bs sx (mergeL Bin sy x)
--     Ini        => unexpected bs2 PC
-- exprStep x        _              bs2 = unexpected bs2 x
--
-- export
-- exprEOI : EEOI b Void (PExpr b) TExpr Expr
-- exprEOI _  (PE Ini _  sx x) = Right (mergeL Bin sx x)
-- exprEOI _  (PE _   bs _  _) = unclosed bs PO
-- exprEOI bs _                = Error.eoi bs
--
-- public export
-- expr : b -> Parser b Void TExpr Expr
-- expr bs = eparser (init bs) (const exprDFA) exprStep exprEOI
--
-- covering
-- main : IO ()
-- main = do
--   putStr "Please enter an expression (q to quit): "
--   s <- getLine
--   case s of
--     ""  => putStrLn "Goodbye!"
--     "q" => putStrLn "Goodbye!"
--     _   => case parseString Virtual (expr Empty) s of
--       Left x  => putStrLn (interpolate x) >> main
--       Right x => putStrLn (interpolate x) >> main

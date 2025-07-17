module Examples.Parse

import Examples.Types
import Examples.Basics
import Text.ILex

%default total

data Tpe = E | O

data PExpr : (tpe : Tpe) -> Type where
  Ini : PExpr O
  PO  : PExpr O -> Bounds -> SnocList (Expr,Op) -> PExpr O
  PE  : PExpr O -> Bounds -> SnocList (Expr,Op) -> Expr -> PExpr E

exprStep : EStep Void PExpr TExpr
exprStep (TLit x) (PO p bs sy)   _   = right $ PE p bs sy (Lit x)
exprStep (TOp o)  (PE p bs sy x) _   = right $ PO p bs $ sy :< (x,o)
exprStep PO       p@(PO {})      bs2 = right $ PO p bs2 [<]
exprStep PC       (PE p _ sy x)  bs2 =
  case p of
    PO p bs sx => right $ PE p bs sx (mergeL Bin sy x)
    Ini        => unexpected bs2 PC
exprStep x        _              bs2 = unexpected bs2 x

exprEOI : EEOI Void PExpr TExpr Expr
exprEOI _  (PE Ini _  sx x) = Right (mergeL Bin sx x)
exprEOI _  (PE _   bs _  _) = unclosed bs PO
exprEOI bs _                = Error.eoi bs

export
expr : Parser Bounds Void TExpr Expr
expr = eparser (PO Ini Empty [<]) (const exprDFA) exprStep exprEOI

covering
main : IO ()
main = do
  putStr "Please enter an expression (q to quit): "
  s <- getLine
  case s of
    ""  => putStrLn "Goodbye!"
    "q" => putStrLn "Goodbye!"
    _   => case parseString Virtual expr s of
      Left x  => putStrLn (interpolate x) >> main
      Right x => putStrLn (interpolate x) >> main

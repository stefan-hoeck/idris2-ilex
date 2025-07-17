module Examples.Parse

import Examples.Types
import Examples.Basics
import Text.ILex.Runner

%default total

data PExpr : Type where
  PO : Bounds -> SnocList (Expr,Op) -> PExpr
  PE : Bounds -> SnocList (Expr,Op) -> Expr -> PExpr

0 SnocStep : (e,s,t : Type) -> Type
SnocStep e s t = Input Bounds (SnocList s) t -> ParseRes Bounds e (SnocList s) t

0 SnocEOI : (e,s,t,a : Type) -> Type
SnocEOI e s t a = Bounds -> SnocList s -> ParseRes Bounds e a t

%inline
append : SnocList s -> s -> ParseRes b e (SnocList s) t
append sv v = Right $ sv:<v

mergeL : Ord o => (o -> e -> e -> e) -> SnocList (e,o) -> e -> e
mergeL merge sp y =
  case sp <>> [] of
    []        => y
    (x,ox)::t => go [<] x ox t y

  where
    app : SnocList (e,o) -> e -> o -> List (e,o) -> e -> e

    go : SnocList (e,o) -> e -> o -> List (e,o) -> e -> e
    go sx x ox []        z =
      case sx of
        [<]        => merge ox x z
        sp:<(w,ow) => go sp w ow [] (merge ox x z)

    go sx x ox ((y,oy) :: xs) z =
      case compare ox oy of
        LT => go (sx:<(x,ox)) y oy xs z
        EQ => go sx (merge ox x y) oy xs z
        GT => app sx (merge ox x y) oy xs z

    app [<]                x ox xs z = go [<] x ox xs z
    app outer@(sp:<(w,ow)) x ox xs z =
      case compare ow ox of
        LT => go outer x ox xs z
        _  => app sp (merge ow w x) ox xs z

merge : Op -> Expr -> Expr -> Expr
merge P = Plus
merge M = Mult
merge X = Exp

exprStep : SnocStep Void PExpr TExpr
exprStep (I x sp bs2) =
  case x of
    TLit v => case sp of
      i:<PO bs sx => append i $ PE bs sx (Lit v)
      _           => unexpected bs2 x

    TOp o => case sp of
      i:<PE bs sx x   => append i $ PO bs (sx :< (x,o))
      _               => unexpected bs2 x

    PO     => case sp of
      _:<PO {}        => append sp $ PO bs2 [<]
      _               => unexpected bs2 x

    PC     => case sp of
      i:<PO bs sx:<PE _ sy y => append i $ PE bs sx (mergeL merge sy y)
      [<PE (BS {}) sy y]     => Right [<PE Empty [<] (mergeL merge sy y)]
      _                      => unexpected bs2 x

exprEoi : SnocEOI Void PExpr TExpr Expr
exprEoi _  [<PE Empty sx x] = Right (mergeL merge sx x)
exprEoi _  (_:<PE bs _ _)   = unclosed bs PO
exprEoi bs _                = Error.eoi bs

export
expr : Parser Bounds Void TExpr Expr
expr = P [<PO Empty [<]] (const exprDFA) exprStep exprEoi

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

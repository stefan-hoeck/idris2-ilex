module Examples.Parse

import Examples.Types
import Examples.Basics
import Text.ILex.Runner

%default total

export
data PExpr : Type where
  PO : Bounds -> SnocList (Expr,Op) -> PExpr
  PE : Bounds -> SnocList (Expr,Op) -> Expr -> PExpr

0 SnocParser : (e,s,t,a : Type) -> Type
SnocParser e s t a = Parser Bounds e (SnocList s) t a

0 SnocStep : (e,s,t : Type) -> Type
SnocStep e s t = Input Bounds (SnocList s) t -> ParseRes Bounds e (SnocList s) t

0 SnocEOI : (e,s,t,a : Type) -> Type
SnocEOI e s t a = SnocList s -> Either (InnerError t e) a

%inline
append : SnocList s -> s -> ParseRes b e (SnocList s) t
append sv v = Step $ sv:<v

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

step : SnocStep Void PExpr TExpr
step (I x sp bs2) =
  case x of
    TLit v => case sp of
      i:<PO bs sx => append i $ PE bs sx (Lit v)
      _           => Err bs2 (Unexpected x)

    TOp o => case sp of
      i:<PE bs sx x   => append i $ PO bs (sx :< (x,o))
      _               => Err bs2 (Unexpected x)

    PO     => case sp of
      _:<PO {}        => append sp $ PO bs2 [<]
      _               => Err bs2 (Unexpected x)

    PC     => case sp of
      i:<PO bs sx:<PE _ sy y => append i $ PE bs sx (mergeL merge sy y)
      [<PE (BS {}) sy y]     => Step [<PE Empty [<] (mergeL merge sy y)]
      _                      => Err bs2 (Unexpected x)

eoi : SnocEOI Void PExpr TExpr Expr
eoi [<PE Empty sx x] = Right (mergeL merge sx x)
eoi _                = Left EOI

export
expr : SnocParser Void PExpr TExpr Expr
expr = P [<PO Empty [<]] (const exprDFA) step Parse.eoi

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

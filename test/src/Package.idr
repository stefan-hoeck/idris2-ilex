module Package

import Text.ILex
import Derive.Prelude

%default total
%language ElabReflection

public export
isIdentStart : Char -> Bool
isIdentStart '_' = True
isIdentStart x   = isUpper x || x > chr 160

public export
isIdentTrailing : Char -> Bool
isIdentTrailing '-'  = True
isIdentTrailing '\'' = True
isIdentTrailing '_'  = True
isIdentTrailing x    = isAlphaNum x || x > chr 160

public export
data Token
  = Comment String
  | EndOfInput
  | Equals
  | DotSepIdent (SnocList String) String
  | Separator
  | Dot
  | LTE
  | GTE
  | LT
  | GT
  | EqOp
  | AndOp
  | Space
  | StringLit String
  | IntegerLit Integer

%runElab derive "Token" [Show,Eq]

public export
ToType Token where
  toType_ = TO $ Plain "Token"

public export
fromIdents : SnocList String -> Token
fromIdents (sx :< x) = DotSepIdent sx x
fromIdents [<]       = EndOfInput -- impossible

public export
comment : SnocList Char -> Token
comment x = Comment (pack (x <>> []))

public export
validStrChar : Char -> Bool
validStrChar '"' = False
validStrChar c   = not (isControl c)

export
ident : {is : _} -> Expr True e is (is:<String)
ident =
  mpred isIdentStart >>> vwrap ->> snocAll (mpred isIdentTrailing) >>- vpack

integer : {is : _} -> Expr True e is (is:<Integer)
integer = (str "-" >>> decimal >>> marr negate) <|> decimal

stringLit : {is : _} -> Expr True e is (is:<String)
stringLit = chr_ '"' >>> many strChar >>> chr_ '"' >>- vpack
  where
    strChar : Expr True e is (is:<Char)
    strChar = (chr_ '\\' >>> dot) <|> mpred validStrChar

export
tok : {is : _} -> Expr True e is (is:<Token)
tok =
      (str "==" $> EqOp)
  <|> (str "--" >>> many dot >>> marr comment)
  <|> (str "=" $> Equals)
  <|> (str "." $> Dot)
  <|> (str "," $> Separator)
  <|> (str "<" $> LT)
  <|> (str ">" $> GT)
  <|> (str "<=" $> LTE)
  <|> (str ">=" $> GTE)
  <|> (str "&&" $> AndOp)
  <|> (space_ >>> ARec space_ $> Space)
  <|> (integer >>> marr IntegerLit)
  <|> (stringLit >>> marr StringLit)
  <|> (sep1 (chr_ '.') ident >>> marr fromIdents)

export
toks : Expr False LexErr [<] [<SnocList Token]
toks = many tok >>> eoi

covering
main : IO ()
main = do
  putStrLn
    """
    module PackageLexer

    import Text.ILex.Util
    import Package

    %default total
    """
  putStrLn (generate "lexTok" toks)

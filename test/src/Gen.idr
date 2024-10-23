module Gen

import Text.ILex
import Language.Reflection

wrap : Val (Integer -> SnocList Integer)
wrap = mlift (\x => [< x])

nats : Expr True LexErr [<] [<SnocList Integer]
nats = natural >>> arr wrap >>> snocAll (chr_ ',' >>> natural) >>> eoi

main : IO ()
main = do
  putStrLn
    """
    module Lexer

    import Text.ILex.Util

    %default total
    """
  putStrLn (generate "lexNat" nats)

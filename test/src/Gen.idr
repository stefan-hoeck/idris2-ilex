module Gen

import Text.ILex
import Language.Reflection

nats : Expr True LexErr [<] [<SnocList $ WBounds Integer]
nats = sep1 (chr_ ',') (bounded natural) >>> eoi

main : IO ()
main = do
  putStrLn
    """
    module Lexer

    import Text.ILex.Util

    %default total
    """
  putStrLn (generate "lexNat" nats)

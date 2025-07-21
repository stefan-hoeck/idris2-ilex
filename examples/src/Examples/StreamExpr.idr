module Examples.StreamExpr

import Examples.Types
import Examples.Basics
import Examples.ParseExpr
import Text.ILex

import FS.Posix
import FS.Posix.Internal
import FS.System
import IO.Async.Loop.Epoll
import IO.Async.Loop.Posix
import Text.ILex.FS

%default total

record State where
  constructor S
  exprs : SnocList Expr
  stack : PExpr StreamBounds tpe

stStep : Step StreamBounds Void State TExpr
stStep t (S se st) bs =
  case exprStep t st bs of
    Left x   => case exprEOI bs st of
      Right x => (\ev => S (se:<x) ev.snd) <$> exprStep t (init zero) bs
      _       => Left x
    Right ev => Right (S se ev.snd)

stChunk : State -> (State, Maybe $ List Expr)
stChunk st@(S [<] _) = (st, Nothing)
stChunk (S sx stack) = (S [<] stack, Just $ sx <>> [])

stEOI : EOI StreamBounds Void State TExpr (List Expr)
stEOI sb (S sx $ PO Ini _ [<]) = Right $ sx <>> []
stEOI sb (S sx stck) = (\x => sx <>> [x]) <$> exprEOI sb stck

export
sexpr : Parser StreamBounds Void TExpr (List Expr)
sexpr =
  P
    (S [<] $ init zero)
    (const exprDFA)
    (\(I x y z) => stStep x y z)
    stChunk
    stEOI

0 Prog : Type -> Type -> Type
Prog o r = AsyncPull Poll o [StreamError TExpr Void, Errno] r

covering
runProg : Prog Void () -> IO ()
runProg prog =
 let handled := handle [stderrLn . interpolate, stderrLn . interpolate] prog
  in epollApp $ mpull handled

streamExprs : Prog String () -> Prog Void ()
streamExprs pths =
     flatMap pths (\p => readBytes p |> P.mapOutput (FileSrc p,))
  |> streamLex sexpr
  |> C.mapOutput interpolate
  |> foreach (writeLines Stdout)
  -- |> C.count
  -- |> foreach (\x => stdoutLn "\{show x} expressions streamed.")

covering
main : IO ()
main = runProg $ streamExprs (P.tail args)

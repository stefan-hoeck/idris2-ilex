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

export
sexpr : Parser StreamBounds Void TExpr (List Expr)
sexpr =
  streamParser (expr zero) $ \case
    Evidence _ (PO Ini _ [<]) => True
    _                         => False

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
  |> streamParse sexpr
  |> C.mapOutput interpolate
  |> foreach (writeLines Stdout)
  -- |> C.count
  -- |> foreach (\x => stdoutLn "\{show x} expressions streamed.")

covering
main : IO ()
main = runProg $ streamExprs (P.tail args)

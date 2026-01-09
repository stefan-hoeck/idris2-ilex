module Examples.JSON

import FS.Posix
import FS.System
import IO.Async.Loop.Epoll
import IO.Async.Loop.Posix
import JSON.Parser
import Text.ILex
import Text.ILex.FS

%default total

export
prettyVal : Interpolation e => Show a => Either e a -> IO ()
prettyVal (Left x)  = putStrLn $ interpolate x
prettyVal (Right v) = printLn v

export
prettyList : Interpolation e => Show a => Either e (List a) -> IO ()
prettyList (Left x)   = putStrLn $ interpolate x
prettyList (Right vs) = traverse_ printLn vs

0 Prog : Type -> Type -> Type
Prog o r = AsyncPull Poll o [ParseError Void, Errno] r

covering
runProg : Prog Void () -> IO ()
runProg prog =
 let handled := handle [stderrLn . interpolate, stderrLn . interpolate] prog
  in epollApp $ mpull handled

streamVals : Prog String () -> Prog Void ()
streamVals pths =
     flatMap pths (\p => streamParse jsonArray (FileSrc p) (readBytes p))
  |> C.count
  |> foreach (\x => stdoutLn "\{show x} values streamed.")

parStreamVals : Prog String () -> Prog Void ()
parStreamVals pths =
     flatMap pths readBytes
  |> lines
  |> parMapI 32 (traverse $ parseBytes json Virtual)
  |> C.count
  |> foreach (\x => stdoutLn "\{show x} values streamed.")

covering
main : IO ()
main = runProg $ parStreamVals (P.tail args)

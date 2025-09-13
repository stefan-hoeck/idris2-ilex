module Spec

import Data.FilePath
import Data.FilePath.File
import FS.Posix
import FS.System
import IO.Async.Loop.Epoll
import IO.Async.Loop.Posix
import JSON.Parser
import Text.ILex.FS
import Text.TOML.Parser
import Text.TOML.Types

testdir : Path Abs
testdir = "/home/gundi/toml/toml-test/tests"

0 Errs : List Type
Errs = [ParseError Void, Errno]

0 AllErrs : List Type
AllErrs = [ParseError TomlParseError, ParseError Void, Errno]

0 Prog : Type -> Type -> Type
Prog o = AsyncPull Poll o Errs

export %inline
readFile : File Abs -> Prog ByteString ()
readFile = readBytes . interpolate

covering
runProg : Prog Void () -> IO ()
runProg prog =
 let handled := handle [stderrLn . interpolate, stderrLn . interpolate] prog
  in epollApp $ mpull handled

invalidTest : Path Rel -> Bool
invalidTest (PRel sp) =
  case sp <>> [] of
    b::bs => b == "invalid"
    _     => True

jval : File Abs -> Prog o JSON
jval p = streamVal JNull json (FileSrc "\{p}") (readFile p)

ttbl : File Abs -> Prog o (Either (ParseError TomlParseError) TomlTable)
ttbl p =
  extractErr _ $
  streamVal {es = AllErrs} empty toml (FileSrc "\{p}") (readBytes "\{p}")

runTest : File Rel -> Prog (Nat,Nat) ()
runTest p =
  let ptoml := testdir </> p <.> "toml"
      pjson := testdir </> p <.> "json"
   in case invalidTest p.parent of
        True => Prelude.do
          Left x <- ttbl ptoml | Right _ => stdoutLn "\{ptoml} should have failed" >> emit (1,1)
          emit (1,0)
        False => Prelude.do
          jv        <- jval pjson
          Right tbl <- ttbl ptoml | Left x => stdoutLn "\{x}" >> emit (1,1)
          emit (1,0)

toPath : ByteString -> Maybe (File Rel)
toPath (BS 0 _) = Nothing
toPath bs       = Prelude.do
  MkF p f <- RelFile.parse (toString bs)
  (n,ext) <- split f
  guard (ext == "toml")
  Just $ MkF p n

add : (Nat,Nat) -> (Nat,Nat) -> (Nat,Nat)
add (a,b) (c,d) = (a+c, b+d)

-- TODO: We should have `foreach` for chunks
testSpec : Prog Void ()
testSpec =
     readFile (testdir /> "files-toml-1.0.0")
  |> lines
  |> C.mapMaybe toPath
  |> bind emits
  |> bind runTest
  |> P.fold add (Z,Z)
  |> foreach (\(t,f) => stdoutLn "Tests run: \{show t}; Tests failed \{show f}")

main : IO ()
main = runProg testSpec

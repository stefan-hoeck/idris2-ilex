module Spec

import Data.FilePath
import Data.FilePath.File
import Data.Linear.Ref1
import FS.Posix
import FS.System
import IO.Async.Loop.Epoll
import IO.Async.Loop.Posix
import JSON.Parser
import System
import Text.ILex
import Text.ILex.FS
import Text.TOML.Parser
import Text.TOML.Types

take : Nat -> String -> String
take n = pack . take n . unpack

dispLT : LocalTime -> String
dispLT (LT h m s ms) =
 let mss := maybe "" (\x => ".\{take 3 $ interpolate x}") ms
  in "\{h}:\{m}:\{s}\{mss}"

dispLDT : LocalDateTime -> String
dispLDT (LDT d t) = "\{d}T\{dispLT t}"

dispODT : OffsetDateTime -> String
dispODT (ODT d $ OT t o) = "\{d}T\{dispLT t}\{o}"

encode : String -> String -> JSON
encode t v = JObject [("type", JString t), ("value", JString v)]

valueToJSON : TomlValue -> JSON

tableToJSON : TomlTable -> JSON
tableToJSON = JObject . SortedMap.toList . map valueToJSON

arrayToJSON : List TomlValue -> JSON
arrayToJSON = JArray . map valueToJSON

valueToJSON (TStr str) = encode "string" str
valueToJSON (TBool x)  = encode "bool" (toLower $ show x)
valueToJSON (TTime (ATLocalDate x))      = encode "date-local" "\{x}"
valueToJSON (TTime (ATLocalTime x))      = encode "time-local" "\{dispLT x}"
valueToJSON (TTime (ATLocalDateTime x))  = encode "datetime-local" "\{dispLDT x}"
valueToJSON (TTime (ATOffsetDateTime x)) = encode "datetime" "\{dispODT x}"
valueToJSON (TInt i)   = encode "integer" (show i)
valueToJSON (TDbl x)   = encode "float" (interpolate x)
valueToJSON (TArr vs)  = arrayToJSON vs
valueToJSON (TTbl x)   = tableToJSON x

adjJSON : JSON -> JSON
adjJSON (JObject [("type", JString "float"),("value", JString v)]) =
  JObject [("type", JString "float"),("value", JDouble $ cast v)]
adjJSON (JObject xs) =
  JObject $ sortBy (comparing fst) (map adjJSON <$> xs)
adjJSON (JArray vs)  = JArray $ map adjJSON vs
adjJSON v            = v

testdir : Path Rel
testdir = "toml/test/suite"

0 Errs : List Type
Errs = [ParseError Void, Errno]

0 AllErrs : List Type
AllErrs = [ParseError TomlParseError, ParseError Void, Errno]

0 Prog : Type -> Type -> Type
Prog o = AsyncPull Poll o Errs

export %inline
readFile : File Rel -> Prog ByteString ()
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

jval : File Rel -> Prog o JSON
jval p = streamVal JNull json (FileSrc "\{p}") (readFile p)

ttbl : File Rel -> Prog o (Either (ParseError TomlParseError) TomlTable)
ttbl p =
  extractErr _ $
  streamVal {es = AllErrs} empty toml (FileSrc "\{p}") (readBytes "\{p}")

runTest : File Rel -> Prog (Nat,Nat) ()
runTest p =
  let ptoml := testdir </> p <.> "toml"
      pjson := testdir </> p <.> "json"
   in case invalidTest p.parent of
        True => Prelude.do
          Left x <- ttbl ptoml
            | Right _ => stdoutLn "\{ptoml} should have failed" >> emit (1,1)
          stdoutLn "\{x}"
          emit (1,0)
        False => Prelude.do
          jv        <- jval pjson
          Right tbl <- ttbl ptoml | Left x => stdoutLn "\{x}" >> emit (1,1)
          case adjJSON jv == adjJSON (tableToJSON tbl) of
            True  => emit (1,0)
            False => Prelude.do
              stdoutLn "\{ptoml}:"
              stdoutLn "expected: \{show jv}"
              stdoutLn "found:    \{show $ tableToJSON tbl}\n"
              emit (1,1)

toPath : ByteString -> Maybe (File Rel)
toPath (BS 0 _) = Nothing
toPath bs       = Prelude.do
  MkF p f <- RelFile.parse (toString bs)
  (n,ext) <- split f
  guard (ext == "toml")
  Just $ MkF p n

add : (Nat,Nat) -> (Nat,Nat) -> (Nat,Nat)
add (a,b) (c,d) = (a+c, b+d)

testSpec : IORef (Nat,Nat) -> Prog Void ()
testSpec ref =
     readFile (testdir /> "files-toml-1.0.0")
  |> lines
  |> C.mapMaybe toPath
  |> bind emits
  |> bind runTest
  |> P.fold add (Z,Z)
  |> foreach (writeref ref)

export
spec : IO ()
spec = do
  ref <- newref (Z,Z)
  runProg (testSpec ref)
  (t,f) <- readref ref
  stdoutLn "Spec tests run: \{show t}; Failed \{show f}"
  when (t == 0 || f > 0) (die "Some spec tests failed")

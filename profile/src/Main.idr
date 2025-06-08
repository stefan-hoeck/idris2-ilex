module Main

import JSON.Parser
import Data.Buffer
import Data.ByteString
import Data.List
import Examples.Basics
import Examples.Types
import Profile
import Text.ILex.Runner

%default total


short : String
short = #"{"Add":{"id":98,"pth":{"PBio":{"path":[1060,186,57]}},"ed":{"name":"Raw Data","path":"Assay_005_MMP-14_SP.xls","comment":"","tags":[],"projects":[7],"created":1528797970229,"modified":{"timestamp":1528797970229,"id":5}}}}"#

long : String
long = fastConcat $ replicate 10 short

extra : String
extra = fastConcat $ replicate 10 long

maxi : String
maxi = fastConcat $ replicate 10 extra

ultra : String
ultra = fastConcat $ replicate 10 maxi

shortBS : (n ** IBuffer n)
shortBS = (_ ** fromString short)

longBS : (n ** IBuffer n)
longBS = (_ ** fromString long)

extraBS : (n ** IBuffer n)
extraBS = (_ ** fromString extra)

maxiBS : (n ** IBuffer n)
maxiBS = (_ ** fromString maxi)

ultraBS : (n ** IBuffer n)
ultraBS = (_ ** fromString ultra)

lexBS : (n ** IBuffer n) -> LexRes Void Examples.Types.JSON
lexBS (n ** buf) = lex Virtual json buf

-- This profiles our JSON lexer against the one from parser-json
-- to know what we are up against.
bench : Benchmark Void
bench = Group "JSON" [
    Single "short"      (basic lexBS shortBS)
  , Single "long"       (basic lexBS longBS)
  , Single "extra"      (basic lexBS extraBS)
  , Single "maxi"       (basic lexBS maxiBS)
  , Single "ultra"      (basic lexBS ultraBS)
  , Single "short lex"  (basic lexJSON short)
  , Single "long lex"   (basic lexJSON long)
  , Single "extra lex"  (basic lexJSON extra)
  , Single "maxi lex"   (basic lexJSON maxi)
  , Single "ultra lex"  (basic lexJSON ultra)
  , Single "short prs"  (basic (parseJSON Virtual) short)
  ]

main : IO ()
main = runDefault (Prelude.const True) Table show bench

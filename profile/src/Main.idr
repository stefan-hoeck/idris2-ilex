module Main

import JSON.Parser
import Data.Buffer
import Data.ByteString
import Data.List
import Examples.JSON
import Language.JSON
import Profile
import Text.ILex

%default total

arr : List String -> String
arr ss = "[" ++ fastConcat (intersperse "," ss) ++ "]"

short : String
short = #"{"Add":{"id":98,"pth":{"PBio":{"path":[1060,186,57]}},"ed":{"name":"Raw Data","path":"Assay_005_MMP-14_SP.xls","comment":"","tags":[],"projects":[7],"created":1528797970229,"modified":{"timestamp":1528797970229,"id":5}}}}"#

long : String
long = arr $ replicate 10 short

extra : String
extra = arr $ replicate 10 long

maxi : String
maxi = arr $ replicate 10 extra

ultra : String
ultra = arr $ replicate 10 maxi

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

lexBS : (n ** IBuffer n) -> ParseRes Void JTok JVal
lexBS (n ** buf) = parse Virtual json buf

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
  , Single "long prs"   (basic (parseJSON Virtual) long)
  , Single "extra prs"  (basic (parseJSON Virtual) extra)
  , Single "maxi prs"   (basic (parseJSON Virtual) maxi)
  , Single "ultra prs"  (basic (parseJSON Virtual) ultra)
  , Single "short ctr"  (basic JSON.parse short)
  , Single "long ctr"   (basic JSON.parse long)
  , Single "extra ctr"  (basic JSON.parse extra)
  , Single "maxi ctr"   (basic JSON.parse maxi)
  , Single "ultra ctr"  (basic JSON.parse ultra)
  ]

main : IO ()
main = runDefault (Prelude.const True) Table show bench

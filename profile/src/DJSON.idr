module DJSON

import Data.String
import Derive.Prelude
import JSON.Parser
import Text.ILex.DStack
import Text.ILex.Util
import Syntax.T1

%default total
%hide Data.Linear.(.)
%hide JSON.Parser.JStr
%language ElabReflection

data JState : List Type -> Type where
  JInit : JState []
  JVal  : JState [JSON]

  JArr  : JState [SnocList JSON]
  JArrV : JState [Void]
  JArrS : JState [Void]

  JObj  : JState [SnocList (String,JSON)]
  JObjL : JState [String,SnocList (String,JSON)]
  JObjC : JState [Void]
  JObjV : JState [Void]
  JObjS : JState [Void]

  JStr  : JState [Void]
  JErr  : JState []

%runElab deriveIndexed "JState" [Show,ConIndex]

DSz : Bits32
DSz = 1 + cast (conIndexJState JErr)

inBoundsJState : (s : JState ts) -> (cast (conIndexJState s) < DSz) === True

export %inline
Cast (JState ts) (Index DSz) where
  cast v = I (cast $ conIndexJState v) @{mkLT $ inBoundsJState v}

public export
0 DSK : Type -> Type
DSK = DStack JState Void

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

parameters {auto sk : DSK q}

  %inline
  jval : JSON -> StateAct q JState DSz
  jval v JArr  (sv::xs)    = putStackAsC (JArr:>(sv:<v)::xs) JArrV
  jval v JObjL (l::sv::xs) = putStackAsC (JObj:>(sv:<(l,v))::xs) JObjV
  jval v JInit x           = dput JVal (v::x)
  jval _ s     x           = derr JErr s x

  %inline
  carr : StateAct q JState DSz
  carr JArr (sv::st:>xs) = jval (JArray $ sv <>> []) st xs
  carr s    x            = derr JErr s x

  %inline
  cobj : StateAct q JState DSz
  cobj JObj (sp::st:>xs) = jval (JObject $ sp <>> []) st xs
  cobj s    x            = derr JErr s x

  %inline
  endstr : String -> StateAct q JState DSz
  endstr s JObj x = dput JObjL (s::x)
  endstr s st   x = jval (JString s) st x

  %inline
  opn : JState [SnocList a] -> F1 q (Index DSz)
  opn s = read1 sk.stack_ >>= \x => dput s ([<]::x)

--------------------------------------------------------------------------------
-- Lexers
--------------------------------------------------------------------------------

%inline
spaced : JState st -> Steps q DSz DSK -> DFA q DSz DSK
spaced x = dfa . jsonSpaced x

codepoint : RExp True
codepoint = #"\u"# >> hexdigit >> hexdigit >> hexdigit >> hexdigit

%inline
valTok : JState st -> Steps q DSz DSK -> DFA q DSz DSK
valTok x ts =
  spaced x $
    [ cexpr "null"  (dact $ jval JNull)
    , cexpr "true"  (dact $ jval $ JBool True)
    , cexpr "false" (dact $ jval $ JBool False)
    , conv (opt '-' >> decimal) (dact . jval . JInteger . integer)
    , read jsonDouble (dact . jval . JDouble . jdouble)
    , copen '{' $ opn JObj
    , copen '[' $ opn JArr
    , copen' '"' JStr
    ] ++ ts

decode : ByteString -> String
decode (BS 6 bv) =
 singleton $ cast {to = Char} $
   hexdigit (bv `at` 2) * 0x1000 +
   hexdigit (bv `at` 3) * 0x100  +
   hexdigit (bv `at` 4) * 0x10   +
   hexdigit (bv `at` 5)
decode _         = "" -- impossible

jchar : RExp True
jchar = range32 0x20 0x10ffff && not '"' && not '\\'

strTok : DFA q DSz DSK
strTok =
  dfa
    [ ccloseStr '"' (dact . endstr)
    , read (plus jchar) (pushStr JStr)
    , cexpr #"\""# (pushStr JStr "\"")
    , cexpr #"\n"# (pushStr JStr "\n")
    , cexpr #"\f"# (pushStr JStr "\f")
    , cexpr #"\b"# (pushStr JStr "\b")
    , cexpr #"\r"# (pushStr JStr "\r")
    , cexpr #"\t"# (pushStr JStr "\t")
    , cexpr #"\\"# (pushStr JStr "\\")
    , cexpr #"\/"# (pushStr JStr "\/")
    , conv codepoint (pushStr JStr . decode)
    ]

--------------------------------------------------------------------------------
-- Parsers
--------------------------------------------------------------------------------

jsonTrans : Lex1 q DSz DSK
jsonTrans =
  lex1
    [ entry JInit $ valTok JInit []
    , entry JVal  $ spaced JVal  []

    , entry JArr  $ valTok JArr [cclose ']' $ dact carr]
    , entry JArrV $ spaced JArrV [cexpr' ',' JArrS, cclose ']' $ dact carr]
    , entry JArrS $ valTok JArrS []

    , entry JObj  $ spaced JObj [cclose '}' $ dact cobj, copen' '"' JStr]
    , entry JObjL $ spaced JObjL [cexpr' ':' JObjC]
    , entry JObjC $ valTok JObjC []
    , entry JObjV $ spaced JObjV [cclose '}' $ dact cobj, cexpr' ',' JObjS]
    , entry JObjS $ spaced JObjS [copen' '"' JStr]

    , entry JStr strTok
    ]

jsonErr : Arr32 DSz (DSK q -> F1 q (BoundedErr Void))
jsonErr =
  errs
    [ entry JArr  $ unclosedIfEOI "[" []
    , entry JArrV $ unclosedIfEOI "[" [",", "]"]
    , entry JArrS $ unclosedIfEOI "[" []
    , entry JObj  $ unclosedIfEOI "{" ["\"", "}"]
    , entry JObjL $ unclosedIfEOI "{" [",", "}"]
    , entry JObjC $ unclosedIfEOI "{" ["\""]
    , entry JObjV $ unclosedIfEOI "{" [":"]
    , entry JObjS $ unclosedIfEOI "{" [":"]
    , entry JStr  $ unclosedIfNLorEOI "\"" []
    ]

jsonEOI : Index DSz -> DSK q -> F1 q (Either (BoundedErr Void) JSON)
jsonEOI st sk =
  read1 sk.stack_ >>= \case
    JVal:>v::_ => pure (Right v)
    _          => arrFail DSK jsonErr st sk

export
djson : P1 q (BoundedErr Void) DSz DSK JSON
djson = P (cast JInit) (init $ JInit:>[]) jsonTrans (\x => (Nothing #)) jsonErr jsonEOI

export %inline
dparseJSON : Origin -> String -> Either (ParseError Void) JSON
dparseJSON = parseString djson

export
testDJSON : String -> IO ()
testDJSON = either (putStrLn . interpolate) printLn . dparseJSON Virtual

--------------------------------------------------------------------------------
-- Streaming
--------------------------------------------------------------------------------
--
-- extract : Part -> (Part, Maybe $ List JSON)
-- extract (PF (JArray vs)) = (PF (JArray []), Just vs)
-- extract (PA PI sv)       = (PA PI [<], maybeList sv)
-- extract (PV sv)          = (PV [<], maybeList sv)
-- extract (PA p sv)        = let (p2,m) := extract p in (PA p2 sv, m)
-- extract (PO p sv)        = let (p2,m) := extract p in (PO p2 sv, m)
-- extract (PL p sv l)      = let (p2,m) := extract p in (PL p2 sv l, m)
-- extract p                = (p, Nothing)
--
-- arrChunk : DSK q -> F1 q (Maybe $ List JSON)
-- arrChunk sk = T1.do
--   p <- getStack
--   let (p2,res) := extract p
--   putStackAs p2 res
--
-- arrEOI : JST -> DSK q -> F1 q (Either (BoundedErr Void) (List JSON))
-- arrEOI st sk t =
--   case st == JIni of
--     True  => case getStack t of
--       PV sv # t => Right (sv <>> []) # t
--       _     # t => Right [] # t
--     False => case jsonEOI st sk t of
--       Right (JArray vs) # t => Right vs # t
--       Right _           # t => Right [] # t
--       Left x            # t => Left x # t
--
-- ||| A parser that is capable of streaming a single large
-- ||| array of JSON values.
-- export
-- jsonArray : P1 q (BoundedErr Void) JSz DSK (List JSON)
-- jsonArray = P JIni (init PI) jsonTrans arrChunk jsonErr arrEOI
--
-- ||| Parser that is capable of streaming large amounts of
-- ||| JSON values.
-- |||
-- ||| Values need not be separated by whitespace but the longest
-- ||| possible value will always be consumed.
-- export
-- jsonValues : P1 q (BoundedErr Void) JSz DSK (List JSON)
-- jsonValues = P JIni (init $ PV [<]) jsonTrans arrChunk jsonErr arrEOI

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

inBoundsJState JInit = Refl
inBoundsJState JVal  = Refl
inBoundsJState JArr  = Refl
inBoundsJState JArrV = Refl
inBoundsJState JArrS = Refl
inBoundsJState JObj  = Refl
inBoundsJState JObjL = Refl
inBoundsJState JObjC = Refl
inBoundsJState JObjV = Refl
inBoundsJState JObjS = Refl
inBoundsJState JStr  = Refl
inBoundsJState JErr  = Refl

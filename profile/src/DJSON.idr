module DJSON

import Data.String
import Derive.Prelude
import JSON.Parser
import Text.ILex.String.DStack
import Text.ILex.Util
import Syntax.T1

%default total
%hide Data.Linear.(.)
%hide JSON.Parser.JStr
%language ElabReflection

data JState : SnocList Type -> Type where
  JInit : JState [<]
  JVal  : JState [<JSON]

  JArr  : JState [<SnocList JSON]
  JArrV : JState [<Void]
  JArrS : JState [<Void]

  JObj  : JState [<SnocList (String,JSON)]
  JObjL : JState [<SnocList (String,JSON),String]
  JObjC : JState [<Void]
  JObjV : JState [<Void]
  JObjS : JState [<Void]

  JStr  : JState [<Void]
  JErr  : JState [<]

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
  jval v JArr  (sx:<sv)    = putStackAsC (sx:<(sv:<v):>JArr) JArrV
  jval v JObjL (sx:<sv:<l) = putStackAsC (sx:<(sv:<(l,v)):>JObj) JObjV
  jval v JInit sx          = dput JVal (sx:<v)
  jval v s     sx          = derr JErr sx s

  %inline
  carr : StateAct q JState DSz
  carr JArr (sx:>st:<sv) = jval (JArray $ sv <>> []) st sx
  carr s    sx           = derr JErr sx s

  %inline
  cobj : StateAct q JState DSz
  cobj JObj (sx:>st:<sp) = jval (JObject $ sp <>> []) st sx
  cobj s    sx           = derr JErr sx s

  %inline
  endstr : String -> StateAct q JState DSz
  endstr s JObj sx = dput JObjL (sx:<s)
  endstr s st   sx = jval (JString s) st sx

  %inline
  opn : JState [<SnocList a] -> F1 q (Index DSz)
  opn s = read1 sk.stack_ >>= \sx => dput s (sx:<[<])

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
    _:<v:>JVal => pure (Right v)
    _          => arrFail DSK jsonErr st sk

public export
djson : P1 q (BoundedErr Void) JSON
djson = P (cast JInit) (init $ [<]:>JInit) jsonTrans (\x => (Nothing #)) jsonErr jsonEOI

export %inline
dparseJSON : Origin -> String -> Either (ParseError Void) JSON
dparseJSON = parseString djson

export
testDJSON : String -> IO ()
testDJSON = either (putStrLn . interpolate) printLn . dparseJSON Virtual

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

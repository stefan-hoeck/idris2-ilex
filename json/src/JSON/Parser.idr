module JSON.Parser

import Data.Buffer
import Data.Linear.Ref1
import Derive.Prelude
import Syntax.T1

import public Text.ILex

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          String Encoding
--------------------------------------------------------------------------------

public export
escape : SnocList Char -> Char -> SnocList Char
escape sc '"'  = sc :< '\\' :< '"'
escape sc '\n' = sc :< '\\' :< 'n'
escape sc '\f' = sc :< '\\' :< 'f'
escape sc '\b' = sc :< '\\' :< 'b'
escape sc '\r' = sc :< '\\' :< 'r'
escape sc '\t' = sc :< '\\' :< 't'
escape sc '\\' = sc :< '\\' :< '\\'
escape sc '/'  = sc :< '\\' :< '/'
escape sc c =
  if isControl c
    then
      let x  := the Integer $ cast c
          d1 := hexChar $ x `div` 0x1000
          d2 := hexChar $ (x `mod` 0x1000) `div` 0x100
          d3 := hexChar $ (x `mod` 0x100)  `div` 0x10
          d4 := hexChar $ x `mod` 0x10
       in sc :< '\\' :< 'u' :< d1 :< d2 :< d3 :< d4
    else sc :< c

public export
encode : String -> String
encode s = pack (foldl escape [<'"'] (unpack s) <>> ['"'])

--------------------------------------------------------------------------------
--          JSON
--------------------------------------------------------------------------------

public export
data JSON : Type where
  JNull   : JSON
  JInteger : Integer -> JSON
  JDouble : Double -> JSON
  JBool   : Bool   -> JSON
  JString : String -> JSON
  JArray  : List JSON -> JSON
  JObject : List (String, JSON) -> JSON

%runElab derive "JSON" [Eq]

showValue : SnocList String -> JSON -> SnocList String

showPair : SnocList String -> (String,JSON) -> SnocList String

showArray : SnocList String -> List JSON -> SnocList String

showObject : SnocList String -> List (String,JSON) -> SnocList String

showValue ss JNull              = ss :< "null"
showValue ss (JInteger ntgr)      = ss :< show ntgr
showValue ss (JDouble dbl)      = ss :< show dbl
showValue ss (JBool True)       = ss :< "true"
showValue ss (JBool False)      = ss :< "false"
showValue ss (JString str)      = ss :< encode str
showValue ss (JArray [])        = ss :< "[]"
showValue ss (JArray $ h :: t)  =
  let ss' = showValue (ss :< "[") h
   in showArray ss' t
showValue ss (JObject [])       = ss :< "{}"
showValue ss (JObject $ h :: t) =
  let ss' = showPair (ss :< "{") h
   in showObject ss' t

showPair ss (s,v) = showValue (ss :< encode s :< ":") v

showArray ss [] = ss :< "]"
showArray ss (h :: t) =
  let ss' = showValue (ss :< ",") h in showArray ss' t

showObject ss [] = ss :< "}"
showObject ss (h :: t) =
  let ss' = showPair (ss :< ",") h in showObject ss' t

showImpl : JSON -> String
showImpl v = fastConcat $ showValue Lin v <>> Nil

export %inline
Show JSON where
  show = showImpl

||| Recursively drops `Null` entries from JSON objects.
export
dropNull : JSON -> JSON

dropNulls : SnocList JSON -> List JSON -> JSON
dropNulls sx []        = JArray $ sx <>> []
dropNulls sx (x :: xs) = dropNulls (sx :< dropNull x) xs

dropNullsP : SnocList (String,JSON) -> List (String,JSON) -> JSON
dropNullsP sx []                = JObject $ sx <>> []
dropNullsP sx ((_,JNull) :: xs) = dropNullsP sx xs
dropNullsP sx ((s,j)     :: xs) = dropNullsP (sx :< (s, dropNull j)) xs

dropNull (JArray xs)  = dropNulls [<] xs
dropNull (JObject xs) = dropNullsP [<] xs
dropNull x            = x

--------------------------------------------------------------------------------
--          Parser State
--------------------------------------------------------------------------------

public export
JSz : Bits32
JSz = 11

public export
0 JST : Type
JST = Index JSz

ANew, AVal, ACom, ONew, OVal, OCom, OLbl, OCol, Str, Done : JST
ANew = 1; AVal = 2; ACom = 3
ONew = 4; OVal = 5; OCom = 6; OLbl = 7; OCol = 8
Str  = 9; Done = 10

data Part : Type where
  PA : Part -> SnocList JSON -> Part -- partial array
  PO : Part -> SnocList (String,JSON) -> Part -- partial object
  PL : Part -> SnocList (String,JSON) -> String -> Part -- partial object
  PI : Part -- initial value
  PV : SnocList JSON -> Part -- initial value for value streaming
  PF : JSON -> Part -- final value

public export
0 SK : Type -> Type
SK = Stack Void Part JSz

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

parameters {auto sk : SK q}

  %inline
  part : JSON -> Part -> F1 q JST
  part v (PA p sy)   = putStackAs (PA p (sy :< v)) AVal
  part v (PL p sy l) = putStackAs (PO p (sy :< (l,v))) OVal
  part v (PV sy)     = putStackAs (PV (sy :< v)) Ini
  part v _           = putStackAs (PF v) Done

  %inline
  onVal : JSON -> F1 q JST
  onVal v = getStack >>= part v

  %inline
  endStr : String -> F1 q JST
  endStr s = T1.do
   getStack >>= \case
     PO a b => putStackAs (PL a b s) OLbl
     p      => part (JString s) p

  %inline
  begin : (Part -> Part) -> JST -> F1 q JST
  begin f st = getStack >>= \p => putStackAs (f p) st

  %inline
  closeVal : F1 q JST
  closeVal =
    getStack >>= \case
      PO p sp => part (JObject $ sp <>> []) p
      PA p sp => part (JArray $ sp <>> []) p
      _       => pure Done

--------------------------------------------------------------------------------
-- Lexers
--------------------------------------------------------------------------------

%inline
spaced : Index r -> Steps q r SK -> DFA q r SK
spaced x = dfa . jsonSpaced x

export
jsonDouble : RExp True
jsonDouble =
  let frac  = '.' >> plus digit
      exp   = oneof ['e','E'] >> opt (oneof ['+','-']) >> plus digit
   in opt '-' >> decimal >> opt frac >> opt exp

%inline
valTok : JST -> Steps q JSz SK -> DFA q JSz SK
valTok x ts =
  spaced x $
    [ cexpr "null"  (onVal JNull)
    , cexpr "true"  (onVal $ JBool True)
    , cexpr "false" (onVal $ JBool False)
    , conv (opt '-' >> decimal) (onVal . JInteger . integer)
    , read jsonDouble (onVal . JDouble . cast)
    , copen '{' (begin (`PO` [<]) ONew)
    , copen '[' (begin (`PA` [<]) ANew)
    , copen' '"' Str
    ] ++ ts

codepoint : RExp True
codepoint = #"\u"# >> hexdigit >> hexdigit >> hexdigit >> hexdigit

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

%inline
strTok : DFA q JSz SK
strTok =
  dfa
    [ ccloseStr '"' endStr
    , read (plus jchar) (pushStr Str)
    , cexpr #"\""# (pushStr Str "\"")
    , cexpr #"\n"# (pushStr Str "\n")
    , cexpr #"\f"# (pushStr Str "\f")
    , cexpr #"\b"# (pushStr Str "\b")
    , cexpr #"\r"# (pushStr Str "\r")
    , cexpr #"\t"# (pushStr Str "\t")
    , cexpr #"\\"# (pushStr Str "\\")
    , cexpr #"\/"# (pushStr Str "\/")
    , conv codepoint (pushStr Str . decode)
    ]

--------------------------------------------------------------------------------
-- Parsers
--------------------------------------------------------------------------------

jsonTrans : Lex1 q JSz SK
jsonTrans =
  lex1
    [ E Ini (valTok Ini [])
    , E Done (spaced Done [])

    , E ANew (valTok ANew [cclose ']' closeVal])
    , E ACom (valTok ACom [])
    , E AVal $ spaced AVal [cexpr' ',' ACom, cclose ']' closeVal]

    , E ONew $ spaced ONew [cclose '}' closeVal, copen' '"' Str]
    , E OVal $ spaced OVal [cclose '}' closeVal, cexpr' ',' OCom]
    , E OCom $ spaced OCom [copen' '"' Str]
    , E OLbl $ spaced OLbl [cexpr' ':' OCol]
    , E OCol (valTok OCol [])

    , E Str strTok
    ]

jsonErr : Arr32 JSz (SK q -> F1 q (BoundedErr Void))
jsonErr =
  arr32 JSz (unexpected [])
    [ E ANew $ unclosedIfEOI "[" []
    , E AVal $ unclosedIfEOI "[" [",", "]"]
    , E ACom $ unclosedIfEOI "[" []
    , E ONew $ unclosedIfEOI "{" ["\"", "}"]
    , E OVal $ unclosedIfEOI "{" [",", "}"]
    , E OCom $ unclosedIfEOI "{" ["\""]
    , E OLbl $ unclosedIfEOI "{" [":"]
    , E OCol $ unclosedIfEOI "{" []
    , E Str  $ unclosedIfNLorEOI "\"" []
    ]

jsonEOI : JST -> SK q -> F1 q (Either (BoundedErr Void) JSON)
jsonEOI sk s t =
  case sk == Done of
    False => arrFail SK jsonErr sk s t
    True  => case getStack t of
      PF v # t => Right v # t
      _    # t => Right JNull # t

export
json : P1 q (BoundedErr Void) JSz SK JSON
json = P Ini (init PI) jsonTrans (\x => (Nothing #)) jsonErr jsonEOI

export %inline
parseJSON : Origin -> String -> Either (ParseError Void) JSON
parseJSON = parseString json

--------------------------------------------------------------------------------
-- Streaming
--------------------------------------------------------------------------------

extract : Part -> (Part, Maybe $ List JSON)
extract (PF (JArray vs)) = (PF (JArray []), Just vs)
extract (PA PI sv)       = (PA PI [<], maybeList sv)
extract (PV sv)          = (PV [<], maybeList sv)
extract (PA p sv)        = let (p2,m) := extract p in (PA p2 sv, m)
extract (PO p sv)        = let (p2,m) := extract p in (PO p2 sv, m)
extract (PL p sv l)      = let (p2,m) := extract p in (PL p2 sv l, m)
extract p                = (p, Nothing)

arrChunk : SK q -> F1 q (Maybe $ List JSON)
arrChunk sk = T1.do
  p <- getStack
  let (p2,res) := extract p
  putStackAs p2 res

arrEOI : JST -> SK q -> F1 q (Either (BoundedErr Void) (List JSON))
arrEOI st sk t =
  case st == Ini of
    True  => case getStack t of
      PV sv # t => Right (sv <>> []) # t
      _     # t => Right [] # t
    False => case jsonEOI st sk t of
      Right (JArray vs) # t => Right vs # t
      Right _           # t => Right [] # t
      Left x            # t => Left x # t

||| A parser that is capable of streaming a single large
||| array of JSON values.
export
jsonArray : P1 q (BoundedErr Void) JSz SK (List JSON)
jsonArray = P Ini (init PI) jsonTrans arrChunk jsonErr arrEOI

||| Parser that is capable of streaming large amounts of
||| JSON values.
|||
||| Values need not be separated by whitespace but the longest
||| possible value will always be consumed.
export
jsonValues : P1 q (BoundedErr Void) JSz SK (List JSON)
jsonValues = P Ini (init $ PV [<]) jsonTrans arrChunk jsonErr arrEOI

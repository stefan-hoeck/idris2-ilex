module JSON.Parser

import Data.Bits
import Data.Buffer
import Data.Linear.Ref1
import Derive.Prelude
import Syntax.T1
import Text.ILex.Derive
import Text.ILex.Util

import public Text.ILex.Bytes

%default total
%hide Data.Linear.(.)
%language ElabReflection

||| We cannot use `cast` to convert all valid JSON numbers
||| to `Double`. Fortunately, both the JavaScript and Scheme
||| backends are more tolerant, so we can use a simple FFI call.
export %foreign "scheme:(lambda (s) (string->number s))"
                "javascript:lambda:(s) => Number(s)"
jdouble : String -> Double

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
          d1 := hexChar $ cast $ (shiftR x 12 .&. 0xf)
          d2 := hexChar $ cast $ (shiftR x 8 .&. 0xf)
          d3 := hexChar $ cast $ (shiftR x 4 .&. 0xf)
          d4 := hexChar $ cast (x .&. 0xf)
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

%runElab deriveParserState "JSz" "JST"
  ["JIni","ANew","AVal","ACom","ONew","OVal","OCom","OLbl","OCol","JStr","JDone"]

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
  part v (PV sy)     = putStackAs (PV (sy :< v)) JIni
  part v _           = putStackAs (PF v) JDone

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
  closeVal : F1 q JST
  closeVal =
    getStack >>= \case
      PO p sp => part (JObject $ sp <>> []) p
      PA p sp => part (JArray $ sp <>> []) p
      _       => pure JDone

--------------------------------------------------------------------------------
-- Lexers
--------------------------------------------------------------------------------

%inline
spaced : Steps q r SK -> DFA q r SK
spaced = dfa . jsonSpaced

export
jsonDouble : RExp True
jsonDouble =
  let frac  = '.' >> plus digit
      exp   = oneof ['e','E'] >> opt (oneof ['+','-']) >> plus digit
   in opt '-' >> decimal >> opt frac >> opt exp

%inline
valTok : Steps q JSz SK -> DFA q JSz SK
valTok ts =
  spaced $
    [ step "null"  (onVal JNull)
    , step "true"  (onVal $ JBool True)
    , step "false" (onVal $ JBool False)
    , bytes (opt '-' >> decimal) (onVal . JInteger . Util.integer)
    , string jsonDouble (onVal . JDouble . jdouble)
    , opn '{' (modStackAs SK (`PO` [<]) ONew)
    , opn '[' (modStackAs SK (`PA` [<]) ANew)
    , opn' '"' JStr
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
    [ closeStr '"' endStr
    , string (plus jchar) (pushStr JStr)
    , step #"\""# (pushStr JStr "\"")
    , step #"\n"# (pushStr JStr "\n")
    , step #"\f"# (pushStr JStr "\f")
    , step #"\b"# (pushStr JStr "\b")
    , step #"\r"# (pushStr JStr "\r")
    , step #"\t"# (pushStr JStr "\t")
    , step #"\\"# (pushStr JStr "\\")
    , step #"\/"# (pushStr JStr "\/")
    , bytes codepoint (pushStr JStr . decode)
    ]

--------------------------------------------------------------------------------
-- Parsers
--------------------------------------------------------------------------------

jsonTrans : Lex1 q JSz SK
jsonTrans =
  lex1
    [ E JIni (valTok [])
    , E JDone (spaced [])

    , E ANew (valTok [close ']' closeVal])
    , E ACom (valTok [])
    , E AVal $ spaced [step' ',' ACom, close ']' closeVal]

    , E ONew $ spaced [close '}' closeVal, opn' '"' JStr]
    , E OVal $ spaced [close '}' closeVal, step' ',' OCom]
    , E OCom $ spaced [opn' '"' JStr]
    , E OLbl $ spaced [step' ':' OCol]
    , E OCol (valTok [])

    , E JStr strTok
    ]

jsonErr : Arr32 JSz (ByteString -> SK q -> F1 q (BBErr Void))
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
    , E JStr $ unclosedIfNLorEOI "\"" []
    ]

jsonEOI : ByteString -> JST -> SK q -> F1 q (Either (BBErr Void) JSON)
jsonEOI bs sk s t =
  case sk == JDone of
    False => arrFail SK jsonErr sk bs s t
    True  => case getStack t of
      PF v # t => Right v # t
      _    # t => Right JNull # t

public export
json : P1 q (BBErr Void) JSON
json = P JIni (init PI) jsonTrans (\x => (Nothing #)) jsonErr jsonEOI

export %inline
parseJSON : Origin -> String -> Either (ParseError Void) JSON
parseJSON = parseStringBB json

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

arrEOI : ByteString -> JST -> SK q -> F1 q (Either (BBErr Void) (List JSON))
arrEOI bs st sk t =
  case st == JIni of
    True  => case getStack t of
      PV sv # t => Right (sv <>> []) # t
      _     # t => Right [] # t
    False => case jsonEOI bs st sk t of
      Right (JArray vs) # t => Right vs # t
      Right _           # t => Right [] # t
      Left x            # t => Left x # t

||| A parser that is capable of streaming a single large
||| array of JSON values.
public export
jsonArray : P1 q (BBErr Void) (List JSON)
jsonArray = P JIni (init PI) jsonTrans arrChunk jsonErr arrEOI

||| Parser that is capable of streaming large amounts of
||| JSON values.
|||
||| Values need not be separated by whitespace but the longest
||| possible value will always be consumed.
public export
jsonValues : P1 q (BBErr Void) (List JSON)
jsonValues = P JIni (init $ PV [<]) jsonTrans arrChunk jsonErr arrEOI

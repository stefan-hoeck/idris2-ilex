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

public export
ANew, AVal, ACom, ONew, OVal, OCom, OLbl, OCol, Str : JST
ANew = 1; AVal = 2; ACom = 3
ONew = 4; OVal = 5; OCom = 6; OLbl = 7; OCol = 8
Str  = 9

public export
data Part : Type where
  PA : Part -> SnocList JSON -> Part -- partial array
  PO : Part -> SnocList (String,JSON) -> Part -- partial object
  PL : Part -> SnocList (String,JSON) -> String -> Part -- partial object
  PI : Part -- initial value
  PV : SnocList JSON -> Part -- initial value for value streaming
  PF : JSON -> Part -- final value

public export
record ST q where
  constructor S
  line : Ref q Nat
  col  : Ref q Nat
  bnds : Ref q (SnocList Bounds)
  part : Ref q Part
  strs : Ref q (SnocList String)

export %inline
LC ST where
  line   = ST.line
  col    = ST.col
  bounds = ST.bnds

export
ini : Part -> F1 q (ST q)
ini prt t =
 let li  # t := ref1 Z t
     co  # t := ref1 Z t
     bs  # t := ref1 [<] t
     pr  # t := ref1 prt t
     ss  # t := ref1 [<] t
  in S li co bs pr ss # t

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

%inline
part : Part -> JSON -> ST q -> F1 q JST
part (PA p sy)   v x = writeAs x.part (PA p (sy :< v)) AVal
part (PL p sy l) v x = writeAs x.part (PO p (sy :< (l,v))) OVal
part (PV sy)     v x = writeAs x.part (PV (sy :< v)) Ini
part _           v x = writeAs x.part (PF v) Done

%inline
onVal : JSON -> ST q -> F1 q JST
onVal v x = read1 x.part >>= \p => part p v x

%inline
endStr : ST q -> F1 q JST
endStr x = T1.do
 s <- getStr x.strs
 read1 x.part >>= \case
   PO a b => writeAs x.part (PL a b s) OLbl
   p      => part p (JString s) x

%inline
begin : (Part -> Part) -> JST -> ST q -> F1 q JST
begin f st x = read1 x.part >>= \p => writeAs x.part (f p) st

%inline
closeVal : ST q -> F1 q JST
closeVal x =
  read1 x.part >>= \case
    PO p sp => part p (JObject $ sp <>> []) x
    PA p sp => part p (JArray $ sp <>> []) x
    _       => pure Done

--------------------------------------------------------------------------------
-- Lexers
--------------------------------------------------------------------------------

%inline
spaced : Index r -> TokenMap (Step1 q e r ST) -> DFA (Step1 q e r ST)
spaced x = dfa Err . jsonSpaced x

export
jsonDouble : RExp True
jsonDouble =
  let frac  = '.' >> plus digit
      exp   = oneof ['e','E'] >> opt (oneof ['+','-']) >> plus digit
   in opt '-' >> decimal >> opt frac >> opt exp

%inline
valTok : JST -> TokenMap (Step1 q e JSz ST) -> DFA (Step1 q e JSz ST)
valTok x ts =
  spaced x $
    [ str "null"  (onVal JNull)
    , str "true"  (onVal $ JBool True)
    , str "false" (onVal $ JBool False)
    , conv (opt '-' >> decimal) (onVal . JInteger . integer)
    , read jsonDouble (onVal . JDouble . cast)
    , copen '{' (begin (`PO` [<]) ONew)
    , copen '[' (begin (`PA` [<]) ANew)
    , copen '"' (const ST Str)
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

%inline
strTok : DFA (Step1 q e JSz ST)
strTok =
  dfa Err
    [ cclose '"' endStr
    , read (plus $ dot && not '"' && not '\\') (push ST strs Str)
    , str #"\""# (push ST strs Str "\"")
    , str #"\n"# (push ST strs Str "\n")
    , str #"\f"# (push ST strs Str "\f")
    , str #"\b"# (push ST strs Str "\b")
    , str #"\r"# (push ST strs Str "\r")
    , str #"\t"# (push ST strs Str "\t")
    , str #"\\"# (push ST strs Str "\\")
    , str #"\/"# (push ST strs Str "\/")
    , conv codepoint (push ST strs Str . decode)
    ]

--------------------------------------------------------------------------------
-- Parsers
--------------------------------------------------------------------------------

json1 : Lex1 q e JSz ST
json1 =
  lex1
    [ E Ini (valTok Ini [])
    , E Done (spaced Done [])

    , E ANew (valTok ANew [cclose ']' closeVal])
    , E ACom (valTok ACom [])
    , E AVal $ spaced AVal [chr' ',' ACom, cclose ']' closeVal]

    , E ONew $ spaced ONew [cclose '}' closeVal, copen '"' (const ST Str)]
    , E OVal $ spaced OVal [cclose '}' closeVal, chr' ',' OCom]
    , E OCom $ spaced OCom [copen '"' (const ST Str)]
    , E OLbl $ spaced OLbl [chr' ':' OCol]
    , E OCol (valTok OCol [])

    , E Str strTok
    ]

jsonErr : Arr32 JSz (ST q -> ByteString -> F1 q (BoundedErr e))
jsonErr =
  arr32 JSz (unexpected [])
    [ E ANew $ unclosed "[" []
    , E AVal $ unclosed "[" [",", "]"]
    , E ACom $ unclosed "[" []
    , E ONew $ unclosed "{" ["\"", "}"]
    , E OVal $ unclosed "{" [",", "}"]
    , E OCom $ unclosed "{" ["\""]
    , E OLbl $ unclosed "{" [":"]
    , E OCol $ unclosed "{" []
    , E Str  $ unclosed "\"" []
    ]

jsonEOI : JST -> ST q -> F1 q (Either (BoundedErr e) JSON)
jsonEOI sk s t =
  case sk == Done of
    False => arrFail ST jsonErr sk s "" t
    True  => case read1 s.part t of
      PF v # t => Right v # t
      _    # t => Right JNull # t

export
json : P1 q (BoundedErr Void) JSz ST JSON
json = P Ini (ini PI) json1 (\x => (Nothing #)) jsonErr jsonEOI

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

arrChunk : ST q -> F1 q (Maybe $ List JSON)
arrChunk sk = T1.do
  p <- read1 sk.part
  let (p2,res) := extract p
  writeAs sk.part p2 res

arrEOI : JST -> ST q -> F1 q (Either (BoundedErr Void) (List JSON))
arrEOI st sk t =
  case st == Ini of
    True  => case read1 sk.part t of
      PV sv # t => Right (sv <>> []) # t
      _     # t => Right [] # t
    False => case jsonEOI st sk t of
      Right (JArray vs) # t => Right vs # t
      Right _           # t => Right [] # t
      Left x            # t => Left x # t

||| A parser that is capable of streaming a single large
||| array of JSON values.
export
jsonArray : P1 q (BoundedErr Void) JSz ST (List JSON)
jsonArray = P Ini (ini PI) json1 arrChunk jsonErr arrEOI

||| Parser that is capable of streaming large amounts of
||| JSON values.
|||
||| Values need not be separated by whitespace but the longest
||| possible value will always be consumed.
export
jsonValues : P1 q (BoundedErr Void) JSz ST (List JSON)
jsonValues = P Ini (ini $ PV [<]) json1 arrChunk jsonErr arrEOI

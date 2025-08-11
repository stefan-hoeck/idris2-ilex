module JSON.Parser

import Derive.Prelude
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
-- Token Type
--------------------------------------------------------------------------------

public export
data JTok : Type where
  Comma : JTok
  Colon : JTok
  JV    : JSON -> JTok
  JStr  : String -> JTok
  Quote : JTok
  PO    : JTok
  PC    : JTok
  BO    : JTok
  BC    : JTok
  NL    : JTok

%runElab derive "JTok" [Show,Eq]

export
Interpolation JTok where
  interpolate Comma      = "','"
  interpolate Colon      = "':'"
  interpolate (JV x)     = show x
  interpolate (JStr str) = show str
  interpolate Quote      = "'\"'"
  interpolate PO         = "'['"
  interpolate PC         = "']'"
  interpolate BO         = "'{'"
  interpolate BC         = "'}'"
  interpolate NL         = "line break"

--------------------------------------------------------------------------------
-- Regular DFA
--------------------------------------------------------------------------------

spaces : RExp True
spaces = plus (oneof [' ', '\n', '\r', '\t'])

double : RExp True
double =
  let frac  = '.' >> plus digit
      exp   = oneof ['e','E'] >> opt (oneof ['+','-']) >> plus digit
   in opt '-' >> decimal >> opt frac >> opt exp

jsonDFA : DFA e JTok
jsonDFA =
  dfa
    [ ("null"            , const $ JV JNull)
    , ("true"            , const $ JV (JBool True))
    , ("false"           , const $ JV (JBool False))
    , ('{'               , const BO)
    , ('}'               , const BC)
    , ('['               , const PO)
    , (']'               , const PC)
    , (','               , const Comma)
    , (':'               , const Colon)
    , ('"'               , const Quote)
    , (opt '-' >> decimal, bytes (JV . JInteger . integer))
    , (double            , txt (JV . JDouble . cast))
    , (spaces            , Ignore)
    ]

--------------------------------------------------------------------------------
-- String Literals
--------------------------------------------------------------------------------

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

strDFA : DFA e JTok
strDFA =
  dfa
    [ ('"', const Quote)
    , ('\n', const NL)
    , (plus (dot && not '"' && not '\\'), txt JStr)
    , (#"\""#, const $ JStr "\"")
    , (#"\n"#, const $ JStr "\n")
    , (#"\f"#, const $ JStr "\f")
    , (#"\b"#, const $ JStr "\b")
    , (#"\r"#, const $ JStr "\r")
    , (#"\t"#, const $ JStr "\t")
    , (#"\\"#, const $ JStr "\\")
    , (#"\/"#, const $ JStr "\/")
    , (codepoint, bytes (JStr . decode))
    ]

--------------------------------------------------------------------------------
-- Parser
--------------------------------------------------------------------------------

data Part : Type -> Type where
  PArr : b -> SnocList JSON -> Part b
  PObj : b -> SnocList (String,JSON) -> String -> Part b

0 Parts : Type -> Type
Parts = SnocList . Part

export
data ST : Type -> Type where
  SI  : ST b
  SV  : JSON -> ST b
  Arr : Parts b -> b -> SnocList JSON -> SepTag -> ST b
  Prs : Parts b -> b -> SnocList (String,JSON) -> SepTag -> ST b
  Obj : Parts b -> b -> SnocList (String,JSON) -> String -> SepTag -> ST b
  Str : Parts b -> b -> SnocList String -> ST b
  Lbl : Parts b -> b -> SnocList (String,JSON) -> b -> SnocList String -> ST b

part : Parts b -> JSON -> ST b
part [<]               v = SV v
part (p:<PArr bs sx)   v = Arr p bs (sx:<v) Val
part (p:<PObj bs sx l) v = Prs p bs (sx:<(l,v)) Val

step : Step b e (ST b) JTok
step tok st bs = case st of
  SI               => case tok of
    JV x   => Right $ SV x
    Quote  => Right $ Str [<] bs [<]
    PO     => Right $ Arr [<] bs [<] New
    BO     => Right $ Prs [<] bs [<] New
    _      => unexpected bs tok

  SV x             => unexpected bs tok

  Arr sx x sy t    => case tok of
    Comma  => sep t (Arr sx x sy Sep) bs tok
    JV v   => val t (Arr sx x (sy:<v) Val) bs tok
    Quote  => val t (Str (sx :< PArr x sy) bs [<]) bs tok
    PO     => val t (Arr (sx :< PArr x sy) bs [<] New) bs tok
    BO     => val t (Prs (sx :< PArr x sy) bs [<] New) bs tok
    PC     => close t (part sx (JArray $ sy <>> [])) bs tok
    _      => unexpected bs tok

  Prs sx x sy t    => case tok of
    Comma  => sep t (Prs sx x sy Sep) bs tok
    Quote  => val t (Lbl sx x sy bs [<]) bs tok
    BC     => close t (part sx (JObject $ sy <>> [])) bs tok
    _      => unexpected bs tok

  Obj sx x sy l t  => case tok of
    Colon  => sep t (Obj sx x sy l Sep) bs tok
    JV v   => val t (Prs sx x (sy:<(l,v)) Val) bs tok
    Quote  => val t (Str (sx :< PObj x sy l) bs [<]) bs tok
    PO     => val t (Arr (sx :< PObj x sy l) bs [<] New) bs tok
    BO     => val t (Prs (sx :< PObj x sy l) bs [<] New) bs tok
    _      => unexpected bs tok

  Str sx x ss      => case tok of
    JStr s => Right $ Str sx x (ss:<s)
    Quote  => Right $ part sx (JString $ snocPack ss)
    _      => unexpected bs tok

  Lbl sx x sy y ss => case tok of
    JStr s => Right $ Lbl sx x sy y (ss:<s)
    Quote  => Right $ Obj sx x sy (snocPack ss) Val
    _      => unexpected bs tok

chunk : ST b -> (ST b, Maybe JSON)
chunk st = (st, Nothing)

jeoi : EOI b e (ST b) JTok JSON
jeoi _  (SV x)          = Right x
jeoi _  (Arr _ x _ _)   = unclosed x PO
jeoi _  (Prs _ x _ _)   = unclosed x BO
jeoi _  (Obj _ x _ _ _) = unclosed x BO
jeoi _  (Str _ x _)     = unclosed x Quote
jeoi _  (Lbl _ x _ _ _) = unclosed x Quote
jeoi bs _               = Error.eoi bs

jdfa : ST b -> DFA e JTok
jdfa (Str {}) = strDFA
jdfa (Lbl {}) = strDFA
jdfa _        = jsonDFA

||| A parser for a single JSON value.
|||
||| See also `jsonValues` and `jsonArray` for streaming versions
||| of JSON parsers.
export
json : Parser b Void JTok JSON
json = P SI jdfa (\(I t s b) => step t s b) chunk jeoi

||| Parses a single string and converts it to a JSON value.
export %inline
parseJSON : Origin -> String -> ParseRes Void JTok JSON
parseJSON o = parseString o json

--------------------------------------------------------------------------------
-- Streaming
--------------------------------------------------------------------------------

export
record StreamST b where
  constructor S
  vals  : SnocList JSON
  state : ST b

valsStep : Step b e (StreamST b) JTok
valsStep tok (S sv (SV v)) bs = S (sv:<v) <$> step tok SI bs
valsStep tok (S sv st)     bs = S sv      <$> step tok st bs

valsChunk : StreamST b -> (StreamST b, Maybe $ List JSON)
valsChunk (S vs st) = (S [<] st, maybeList vs)

valsEOI : EOI b e (StreamST b) JTok (List JSON)
valsEOI _  (S vs SI)     = Right (vs <>> [])
valsEOI _  (S vs (SV v)) = Right (vs <>> [v])
valsEOI bs (S _  st)     = jeoi bs st $> []

||| Parser that is capable of streaming large amounts of
||| JSON values.
|||
||| Values need not be separated by whitespace but the longest
||| possible value will always be consumed.
export
jsonValues : Parser b Void JTok (List JSON)
jsonValues = P (S [<] SI) (jdfa . state) (\(I t s b) => valsStep t s b) valsChunk valsEOI

extract : Parts b -> (Parts b, Maybe $ List JSON)
extract sp =
  case sp <>> [] of
    PArr x sx :: xs => ([<PArr x [<]] <>< xs, maybeList sx)
    ps              => ([<] <>< ps, Nothing)

arrChunk : ST b -> (ST b, Maybe $ List JSON)
arrChunk (SV (JArray vs))     = (SI, Just vs)
arrChunk (Arr sx x sy y)      = let (a,b) := extract sx in (Arr a x sy y, b)
arrChunk (Prs sx x sy y)      = let (a,b) := extract sx in (Prs a x sy y, b)
arrChunk (Obj sx x sy str y)  = let (a,b) := extract sx in (Obj a x sy str y, b)
arrChunk (Str sx x sstr)      = let (a,b) := extract sx in (Str a x sstr, b)
arrChunk (Lbl sx x sy y sstr) = let (a,b) := extract sx in (Lbl a x sy y sstr, b)
arrChunk st                   = (st, Nothing)

arrEOI : EOI b e (ST b) JTok (List JSON)
arrEOI bs SI = Right []
arrEOI bs st =
  case jeoi bs st of
    Right (JArray vs) => Right vs
    Right _           => Error.eoi bs
    Left x            => Left x

||| A parser that is capable of streaming a single large
||| array of JSON values.
export
jsonArray : Parser b Void JTok (List JSON)
jsonArray = P SI jdfa (\(I t s b) => step t s b) arrChunk arrEOI

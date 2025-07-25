module Examples.JSON

import Data.SnocList.Quantifiers
import Text.ILex
import Derive.Prelude

%default total
%language ElabReflection
%hide Data.Linear.(.)

--------------------------------------------------------------------------------
-- JSON values
--------------------------------------------------------------------------------

||| A tree data type for JSON values
public export
data JVal : Type where
  JNull   : JVal
  JInteger : Integer -> JVal
  JDouble : Double -> JVal
  JBool   : Bool   -> JVal
  JString : String -> JVal
  JArray  : List JVal -> JVal
  JObject : List (String, JVal) -> JVal

%runElab derive "JVal" [Show,Eq]

--------------------------------------------------------------------------------
-- Token Type
--------------------------------------------------------------------------------

public export
data JTok : Type where
  Comma : JTok
  Colon : JTok
  JV    : JVal -> JTok
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
  interpolate Comma      = ","
  interpolate Colon      = ":"
  interpolate (JV x)     = show x
  interpolate (JStr str) = str
  interpolate Quote      = "\""
  interpolate PO         = "["
  interpolate PC         = "]"
  interpolate BO         = "{"
  interpolate BC         = "}"
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
    , (opt '-' >> decimal, txt (JV . JInteger . integer))
    , (double            , txt (JV . JDouble . cast . toString))
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
    , (plus (dot && not '"' && not '\\'), txt (JStr . toString))
    , (#"\""#, const $ JStr "\"")
    , (#"\n"#, const $ JStr "\n")
    , (#"\f"#, const $ JStr "\f")
    , (#"\b"#, const $ JStr "\b")
    , (#"\r"#, const $ JStr "\r")
    , (#"\t"#, const $ JStr "\t")
    , (#"\\"#, const $ JStr "\\")
    , (#"\/"#, const $ JStr "\/")
    , (codepoint, txt (JStr . decode))
    ]

--------------------------------------------------------------------------------
-- Parser
--------------------------------------------------------------------------------

public export
data SepTag = New | Val | Sep

%runElab derive "SepTag" [Show,Eq,Ord]

sep : SepTag -> a -> b -> t -> ParseRes b e a t
sep Val v _  _   = Right v
sep _   _ bs tok = unexpected bs tok

val : SepTag -> a -> b -> t -> ParseRes b e a t
val Val _ bs tok = unexpected bs tok
val _   v _  _   = Right v

close : SepTag -> a -> b -> t -> ParseRes b e a t
close Sep _ bs tok = unexpected bs tok
close _   v _  _   = Right v

data Part : Type -> Type where
  PArr : b -> SnocList JVal -> Part b
  PObj : b -> SnocList (String,JVal) -> String -> Part b

0 Parts : Type -> Type
Parts = SnocList . Part

export
data ST : Type -> Type where
  SI  : ST b
  SV  : JVal -> ST b
  Arr : Parts b -> b -> SnocList JVal -> SepTag -> ST b
  Prs : Parts b -> b -> SnocList (String,JVal) -> SepTag -> ST b
  Obj : Parts b -> b -> SnocList (String,JVal) -> String -> SepTag -> ST b
  Str : Parts b -> b -> SnocList String -> ST b
  Lbl : Parts b -> b -> SnocList (String,JVal) -> b -> SnocList String -> ST b

part : Parts b -> JVal -> ST b
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

chunk : ST b -> (ST b, Maybe JVal)
chunk st = (st, Nothing)

jeoi : EOI b e (ST b) JTok JVal
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

export
json : Parser b Void JTok JVal
json = P SI jdfa (\(I t s b) => step t s b) chunk jeoi

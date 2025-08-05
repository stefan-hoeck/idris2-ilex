module Examples.JSON

import Data.SnocList.Quantifiers
import Derive.Prelude
import Text.ILex
import Text.ILex.Debug
import Text.PrettyPrint.Bernardy

import FS.Posix
import FS.Posix.Internal
import FS.System
import IO.Async.Loop.Epoll
import IO.Async.Loop.Posix
import Text.ILex.FS

%default total
%language ElabReflection
%hide Data.Linear.(.)

export
prettyVal : Interpolation e => Show a => Either e a -> IO ()
prettyVal (Left x)  = putStrLn $ interpolate x
prettyVal (Right v) = printLn v

export
prettyList : Interpolation e => Show a => Either e (List a) -> IO ()
prettyList (Left x)   = putStrLn $ interpolate x
prettyList (Right vs) = traverse_ printLn vs

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

export
Pretty JTok where prettyPrec p = line . interpolate

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

||| Parses a single JSON value.
export
json : Parser b Void JTok JVal
json = P SI jdfa (\(I t s b) => step t s b) chunk jeoi

--------------------------------------------------------------------------------
-- Streaming
--------------------------------------------------------------------------------

export
record StreamST b where
  constructor S
  vals  : SnocList JVal
  state : ST b

valsStep : Step b e (StreamST b) JTok
valsStep tok (S sv (SV v)) bs = S (sv:<v) <$> step tok SI bs
valsStep tok (S sv st)     bs = S sv      <$> step tok st bs

valsChunk : StreamST b -> (StreamST b, Maybe $ List JVal)
valsChunk (S vs st) = (S [<] st, maybeList vs)

valsEOI : EOI b e (StreamST b) JTok (List JVal)
valsEOI _  (S vs SI)     = Right (vs <>> [])
valsEOI _  (S vs (SV v)) = Right (vs <>> [v])
valsEOI bs (S _  st)     = jeoi bs st $> []

export
jsonValues : Parser b Void JTok (List JVal)
jsonValues = P (S [<] SI) (jdfa . state) (\(I t s b) => valsStep t s b) valsChunk valsEOI

extract : Parts b -> (Parts b, Maybe $ List JVal)
extract sp =
  case sp <>> [] of
    PArr x sx :: xs => ([<PArr x [<]] <>< xs, maybeList sx)
    ps              => ([<] <>< ps, Nothing)

arrChunk : ST b -> (ST b, Maybe $ List JVal)
arrChunk (SV (JArray vs))     = (SI, Just vs)
arrChunk (Arr sx x sy y)      = let (a,b) := extract sx in (Arr a x sy y, b)
arrChunk (Prs sx x sy y)      = let (a,b) := extract sx in (Prs a x sy y, b)
arrChunk (Obj sx x sy str y)  = let (a,b) := extract sx in (Obj a x sy str y, b)
arrChunk (Str sx x sstr)      = let (a,b) := extract sx in (Str a x sstr, b)
arrChunk (Lbl sx x sy y sstr) = let (a,b) := extract sx in (Lbl a x sy y sstr, b)
arrChunk st                   = (st, Nothing)

arrEOI : EOI b e (ST b) JTok (List JVal)
arrEOI bs SI = Right []
arrEOI bs st =
  case jeoi bs st of
    Right (JArray vs) => Right vs
    Right _           => Error.eoi bs
    Left x            => Left x

export
jsonArray : Parser b Void JTok (List JVal)
jsonArray = P SI jdfa (\(I t s b) => step t s b) arrChunk arrEOI

0 Prog : Type -> Type -> Type
Prog o r = AsyncPull Poll o [StreamError JTok Void, Errno] r

covering
runProg : Prog Void () -> IO ()
runProg prog =
 let handled := handle [stderrLn . interpolate, stderrLn . interpolate] prog
  in epollApp $ mpull handled

streamVals : Prog String () -> Buf -> Prog Void ()
streamVals pths buf =
     flatMap pths (\p => readRawBytes buf p |> P.mapOutput (FileSrc p,))
  |> streamParse1 jsonArray
  -- |> C.mapOutput show
  -- |> foreach (writeLines Stdout)
  |> C.count
  |> foreach (\x => stdoutLn "\{show x} values streamed.")

covering
main : IO ()
main = runProg $ lift1 (buf 0xffff) >>= streamVals (P.tail args)

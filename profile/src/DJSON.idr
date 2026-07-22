module DJSON

import Data.String
import Derive.Prelude
import Text.ILex.Derive
import JSON.Parser
import Text.ILex
import Syntax.T1

%default total
%hide Data.Linear.(.)
%language ElabReflection

public export
data Tag : Type -> Type where
  TArr : Tag (SnocList JSON)
  TObj : Tag (SnocList (String,JSON))
  TLbl : Tag (SnocList (String,JSON),String)
  TVal : Tag JSON
  TIni : Tag ()

public export
data PTag : Type -> Type where
  PArr : PTag (SnocList JSON)
  PLbl : PTag (SnocList (String,JSON),String)
  PIni : PTag ()

public export
record Tagged (t : Type -> Type) where
  constructor T
  {0 type : Type}
  tag : t type
  val : type

public export
0 DHead : Type
DHead = Tagged Tag

public export
0 DPart : Type
DPart = Tagged PTag

toHead : DPart -> DHead
toHead (T PArr val) = T TArr val
toHead (T PLbl val) = T TLbl val
toHead (T PIni val) = T TIni val

appendPart : SnocList DPart -> DHead -> SnocList DPart
appendPart sx (T TArr val) = sx :< T PArr val
appendPart sx (T TLbl val) = sx :< T PLbl val
appendPart sx (T TIni val) = sx :< T PIni val
appendPart sx _ = sx

public export
record DSK (q : Type) where
  [search q]
  constructor S
  -- Position and token bounds
  bufSize_    : Nat
  prev_       : ByteString
  cur_        : IBuffer bufSize_
  prevOffset_ : Nat
  curOffset_  : Nat
  from_       : Ref q (LTENat bufSize_)
  till_       : Ref q (LTENat bufSize_)
  positions_  : Ref q (SnocList BytePos)

  -- Custom stack type
  stack_     : Ref q (SnocList DPart)

  -- Current state
  head       : Ref q DHead

  -- Working with string literals
  strings_   : Ref q (SnocList String)

  -- Error handling
  error_     : Ref q (Maybe $ BBErr Void)

%runElab derive "DSK" [FullStack]

||| Initializes a new parser stack.
export
init : (n : Nat) -> IBuffer n -> F1 q (DSK q)
init n buf = T1.do
  rf <- ref1 (first n)
  rt <- ref1 (first n)
  ps <- ref1 [<]
  sk <- ref1 [<]
  st <- ref1 (T TIni ())
  ss <- ref1 [<]
  er <- ref1 Nothing
  pure (S n empty buf 0 0 rf rt ps sk st ss er)

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

parameters {auto sk : DSK q}

  %inline
  part : JSON -> DHead -> F1 q JST
  part v (T tg x) =
    case tg of
      TArr => writeAs sk.head (T TArr $ x:<v) AVal
      TLbl => writeAs sk.head (T TObj $ (fst x:< (snd x, v))) OVal
      _    => writeAs sk.head (T TVal v) JDone

  %inline
  onVal : JSON -> F1 q JST
  onVal v = read1 sk.head >>= part v

  %inline
  endStr : String -> F1 q JST
  endStr s =
   read1 sk.head >>= \case
     T TObj x => writeAs sk.head (T TLbl (x,s)) OLbl
     p        => part (JString s) p

  %inline
  closeVal : F1 q JST
  closeVal = T1.do
    (sx:<x) <- read1 sk.stack_ | [<] => pure JDone
    write1 sk.stack_ sx
    read1 sk.head >>= \case
      T TObj sp => part (JObject $ sp <>> []) (toHead x)
      T TArr sp => part (JArray $ sp <>> []) (toHead x)
      _         => pure JDone

  %inline
  openHead : DHead -> JST -> F1 q JST
  openHead h res = T1.do
    sx <- read1 sk.stack_
    ho <- read1 sk.head
    write1 sk.stack_ (appendPart sx ho)
    writeAs sk.head h res

--------------------------------------------------------------------------------
-- Lexers
--------------------------------------------------------------------------------

%inline
spaced : Steps q r DSK -> DFA q r DSK
spaced = dfa . jsonSpaced

%inline
valTok : Steps q JSz DSK -> DFA q JSz DSK
valTok ts =
  spaced $
    [ step "null"  (onVal JNull)
    , step "true"  (onVal $ JBool True)
    , step "false" (onVal $ JBool False)
    , bytes (opt '-' >> decimal) (onVal . JInteger . Util.integer)
    , string jsonDouble (onVal . JDouble . jdouble)
    , opn '{' (openHead (T TObj [<]) ONew)
    , opn '[' (openHead (T TArr [<]) ANew)
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
strTok : DFA q JSz DSK
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

jsonTrans : Lex1 q JSz DSK
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

jsonErr : Arr32 JSz (DSK q -> F1 q (BBErr Void))
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

jsonEOI : JST -> DSK q -> F1 q (Either (BBErr Void) JSON)
jsonEOI st sk t =
  case st == JDone of
    False => arrFail DSK jsonErr st sk t
    True  => case read1 sk.head t of
      T TVal v # t => Right v # t
      _        # t => Right JNull # t

public export
json2 : P1 q (BBErr Void) JSON
json2 = P JIni init jsonTrans (\x => (Nothing #)) jsonErr jsonEOI

export %inline
parseJSON2 : Origin -> String -> Either (ParseError Void) JSON
parseJSON2 = parseString json2

module Text.TOML.Parser

import Data.SortedMap
import Data.String
import Data.Linear.Ref1
import Text.ILex.Derive
import Text.ILex
import Text.TOML.Lexer
import Text.TOML.Types
import Text.TOML.Internal.TStack
import Syntax.T1

%hide Data.Linear.(.)
%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Parser Stack
--------------------------------------------------------------------------------

export
data TStack : Type where
  STbl : TreeTable -> SnocList Key -> TStack
  SArr : TreeTable -> SnocList Key -> TStack
  STop : TView Tree -> SnocList Key -> TreeTable -> TStack
  VArr : TStack -> SnocList TomlValue -> TStack
  VTbl : TStack -> SnocList Key -> TreeTable -> TStack

toRoot : TStack -> TreeTable
toRoot (STbl t sk)   = t
toRoot (SArr t sk)   = t
toRoot (STop v sk t) = reduceT Undef t (tagAsHDef v)
toRoot (VArr x sv)   = toRoot x
toRoot (VTbl x sk y) = toRoot x

toTable : TStack -> Either e TomlTable
toTable = Right . toTbl . toRoot

empty : TStack
empty = STop VR [<] empty

--------------------------------------------------------------------------------
-- States
--------------------------------------------------------------------------------

-- TOML Parser states: `TSz` is the number of states, `TST` is an alias
-- for `Index TSz`.
%runElab deriveParserState "TSz" "TST"
  [ "TIni", "EKey", "ESep", "EVal", "EOL", "Err", "TSep", "ASep"
  -- arrays and inline tables (`Val` after value, `Com` after comma)
  , "ANew", "AVal", "ACom", "TVal", "TCom", "TNew"
  -- quoted keys and strings
  , "QKey", "LKey", "QStr", "LStr", "MLQStr", "MLLStr"
  ]

public export
0 TSTCK : Type -> Type
TSTCK = Stack TomlParseError TStack TSz

--------------------------------------------------------------------------------
-- Tables and Values
--------------------------------------------------------------------------------

parameters {auto sk : TSTCK q}

  addkey : KeyType -> ByteBounded String -> F1 q TST
  addkey kt (B s bs) =
   let k := KT s kt bs
    in getStack >>= \case
         STbl x ks   => putStackAs (STbl x $ ks:<k) TSep
         SArr x ks   => putStackAs (SArr x $ ks:<k) ASep
         STop x ks t => putStackAs (STop x (ks:<k) t) ESep
         VTbl x ks t => putStackAs (VTbl x (ks:<k) t) ESep
         VArr x sv   => putStackAs (VArr x sv) Err

  onkey : String -> F1 q TST
  onkey s = T1.do
    bs <- Interfaces.bounds
    addkey Plain (B s bs)

  escape : TST -> ByteString -> F1 q TST
  escape res bs =
   let hex := cast {to = Bits32} $ hexadecimal (drop 2 bs)
    in case has unicode hex && not (has surrogate hex) of
         True  => pushBits32 res hex
         False => unexpected [] sk >>= flip failWith Err

  end : TST -> Either TErr TStack -> F1 q TST
  end x (Left y)  = failWith y Err
  end x (Right y) = putStackAs y x

  onval : TomlValue -> TStack -> F1 q TST
  onval v (STop x sk t) = end EOL  $ STop x [<] <$> addVal t sk v
  onval v (VArr x sv)   = end AVal $ Right (VArr x (sv:<v))
  onval v (VTbl x sk t) = end TVal $ VTbl x [<] <$> addVal t sk v
  onval v s             = end Err (Right s)

  openStdTable : F1 q TST
  openStdTable = getStack >>= \s => putStackAs (STbl (toRoot s) [<]) EKey

  openArrayTable : F1 q TST
  openArrayTable = getStack >>= \s => putStackAs (SArr (toRoot s) [<]) EKey

  openArray : F1 q TST
  openArray = getStack >>= \s => putStackAs (VArr s [<]) ANew

  openInlineTable : F1 q TST
  openInlineTable = getStack >>= \s => putStackAs (VTbl s [<] empty) TNew

  close : F1 q TST
  close =
    getStack >>= \case
      STbl t sk =>
        case tview t (sk <>> []) of
          Right (v,t) => putStackAs (STop v [<] t) EOL
          Left  x     => failWith x Err
      SArr t sk =>
        case view VR t (sk <>> []) of
          Right (VT v t k New,t2) => putStackAs (STop (VA v t k [<]) [<] t2) EOL
          Right (VA v t k st,t2)  => putStackAs (STop (VA v t k (st:<t2)) [<] empty) EOL
          Right (v,_)             => failWith (vexists v) Err
          Left  x                 => failWith x Err
      VArr x sx   => onval (TArr $ sx <>> []) x
      VTbl x sk t => onval (TTbl $ toTbl t) x
      s           => end Err (Right s)

  qstr : String -> F1 q TST
  qstr s = getStack >>= onval (TStr s)

%inline
val : a -> (ByteString -> TomlValue) -> (a, Step q TSz TSTCK)
val x f = bytes x $ \bs => getStack >>= onval (f bs)

valE : a -> (ByteString -> AnyTime) -> (a, Step q TSz TSTCK)
valE x f =
  bytes x $ \bs => case extraCheckDate (f bs) of
    Right v => getStack >>= onval (TTime v)
    Left  x => raise (Custom $ InvalidLeapDay x) (size bs) Err

%inline
val' : a -> TomlValue -> (a, Step q TSz TSTCK)
val' x = val x . const

--------------------------------------------------------------------------------
-- Lexer Steps
--------------------------------------------------------------------------------

tomlSpaced : Steps q TSz TSTCK -> DFA q TSz TSTCK
tomlSpaced ss = dfa $ ignore' (plus wschar) :: ss

tomlIgnore : TST -> Steps q TSz TSTCK -> DFA q TSz TSTCK
tomlIgnore nl ss = tomlSpaced $ [ignore' comment, step' newline nl] ++ ss

keySteps : Steps q TSz TSTCK
keySteps =
  [ string unquotedKey onkey
  , opn' '\'' LKey
  , opn' '"'  QKey
  ]

valSteps : Steps q TSz TSTCK
valSteps =
  [ val' "true"  (TBool True)
  , val' "false" (TBool False)

  -- integers
  , val  decInt  (TInt . readDecInt)
  , val  binInt  (TInt . binarySep . drop 2)
  , val  octInt  (TInt . octalSep underscore . drop 2)
  , val  hexInt  (TInt . hexadecimalSep underscore . drop 2)

  -- floats
  , val' nan     (TDbl NaN)
  , val' posInf  (TDbl $ Infty Plus)
  , val' "-inf"  (TDbl $ Infty Minus)
  , val float    (TDbl . readFloat)

  -- Date and Time
  , valE fullDate  (ATLocalDate . readLocalDate)
  , valE (fullDate >> ' ')  (ATLocalDate . readLocalDate . trim)
  , valE localTime (ATLocalTime . readLocalTime)
  , valE localDateTime (ATLocalDateTime . readLocalDateTime)
  , valE offsetDateTime (ATOffsetDateTime . readOffsetDateTime)

  -- Nested Values
  , opn '[' openArray
  , opn '{' openInlineTable

  -- Strings
  , opn' '"'  QStr
  , opn' '\'' LStr
  , opn' #"""""# MLQStr
  , opn' (#"""""# >> newline) MLQStr
  , opn' "'''" MLLStr
  , opn' ("'''" >> newline) MLLStr
  , val' #""""# (TStr "")
  , val' #"''"# (TStr "")
  ]

escapes : TST -> Steps q TSz TSTCK
escapes res =
    [ string (plus basicUnescaped) (pushStr res)
    , step #"\""# (pushStr res "\"")
    , step #"\\"# (pushStr res "\\")
    , step #"\b"# (pushStr res "\b")
    , step #"\e"# (pushStr res "\e")
    , step #"\f"# (pushStr res "\f")
    , step #"\n"# (pushStr res "\n")
    , step #"\r"# (pushStr res "\r")
    , step #"\t"# (pushStr res "\t")
    , bytes ("\\u" >> repeat 4 hexdigit) (escape res)
    , bytes ("\\U" >> repeat 8 hexdigit) (escape res)
    ]

mlqDFA : DFA q TSz TSTCK
mlqDFA =
  dfa $
    [ closeStr #"""""# qstr
    , close #""""""# (pushStr' "\"" >> getStr >>= qstr)
    , close #"""""""# (pushStr' "\"\"" >> getStr >>= qstr)
    , step #"""# (pushStr MLQStr "\"")
    , step #""""# (pushStr MLQStr "\"\"")
    , step newline (pushStr MLQStr "\n")
    , step' mlbEscapedNL MLQStr
    ] ++ escapes MLQStr

mllDFA : DFA q TSz TSTCK
mllDFA =
  dfa $
    [ closeStr "'''" qstr
    , close "''''" (pushStr' "'" >> getStr >>= qstr)
    , close "'''''" (pushStr' "''" >> getStr >>= qstr)
    , step "'" (pushStr MLLStr "'")
    , step "''" (pushStr MLLStr "''")
    , step newline (pushStr MLLStr "\n")
    , string literalChars (pushStr MLLStr)
    ]

--------------------------------------------------------------------------------
-- State Transitions
--------------------------------------------------------------------------------

tomlTrans : Lex1 q TSz TSTCK
tomlTrans =
  lex1
    [ E TIni $ tomlIgnore TIni (keySteps ++ [opn '[' openStdTable, opn "[[" openArrayTable])
    , E ESep $ tomlSpaced [step' '.' EKey, step' '=' EVal]
    , E TSep $ tomlSpaced [step' '.' EKey, close ']' close]
    , E ASep $ tomlSpaced [step' '.' EKey, close "]]" close]
    , E EKey $ tomlSpaced keySteps
    , E EVal $ tomlSpaced valSteps
    , E ANew $ tomlIgnore ANew (close ']' close :: valSteps)
    , E AVal $ tomlIgnore AVal [close ']' close, step' ',' ACom]
    , E ACom $ tomlIgnore ACom (close ']' close :: valSteps)
    , E QKey $ dfa $ closeBoundedStr '"' (addkey Quoted) :: escapes QKey
    , E LKey $ dfa [closeBoundedStr '\'' (addkey Plain), string literalChars (pushStr LKey)]
    , E QStr $ dfa $ closeStr '"' qstr :: escapes QStr
    , E LStr $ dfa [closeStr '\'' qstr, string literalChars (pushStr LStr)]
    , E MLQStr mlqDFA
    , E MLLStr mllDFA
    , E TVal $ tomlSpaced [step' ',' TCom, close '}' close]
    , E TNew $ tomlSpaced (close '}' close :: keySteps)
    , E TCom $ tomlSpaced keySteps
    , E EOL  $ tomlIgnore TIni []
    ]

tomlErr : Arr32 TSz (TSTCK q -> F1 q TErr)
tomlErr =
  arr32 TSz (unexpected [])
    [ E ANew $ unclosedIfEOI "[" []
    , E AVal $ unclosedIfEOI "[" [",", "]"]
    , E ACom $ unclosedIfEOI "[" []
    , E TVal $ unclosedIfNLorEOI "{" [",", "}"]
    , E TCom $ unclosedIfNLorEOI "{" []
    , E TNew $ unclosedIfNLorEOI "{" []
    , E QStr $ unclosedIfNLorEOI "\"" []
    , E QKey $ unclosedIfNLorEOI "\"" []
    , E LStr $ unclosedIfNLorEOI "'" []
    , E LKey $ unclosedIfNLorEOI "'" []
    , E MLQStr $ unclosedIfEOI "\"\"\"" []
    , E MLLStr $ unclosedIfEOI "'''" []
    , E ESep $ unexpected [".", "="]
    , E TSep $ unclosedIfNLorEOI "[" [".", "]"]
    , E ASep $ unclosedIfNLorEOI "[[" [".", "]]"]
    ]

tomlEOI : TST -> TSTCK q -> F1 q (Either TErr TomlTable)
tomlEOI st sk =
  case st == TIni || st == EOL of
    False => arrFail TSTCK tomlErr st sk
    True  => getStack >>= pure . toTable

public export
toml : P1 q TErr TomlTable
toml = P TIni (init empty) tomlTrans (\x => (Nothing #)) tomlErr tomlEOI

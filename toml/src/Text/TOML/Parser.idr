module Text.TOML.Parser

import Data.SortedMap
import Data.String
import Data.Linear.Ref1
import Text.ILex
import Text.TOML.Lexer
import Text.TOML.Types
import Text.TOML.Internal.TStack
import Syntax.T1

%hide Data.Linear.(.)
%default total

--------------------------------------------------------------------------------
--          Parser Stack
--------------------------------------------------------------------------------

export
data TStack : Type where
  STbl : TreeTable -> SnocList Key -> TStack
  SArr : TreeTable -> SnocList Key -> TStack
  STop : TView Tree -> SnocList Key -> TreeTable -> TStack
  VArr : TStack -> SnocList TomlValue -> TStack
  VTbl : TStack -> SnocList Key -> TomlTable -> TStack

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

public export
TSz : Bits32
TSz = 20

public export
TST : Type
TST = Index TSz

-- Keys and utilities:
-- EKey, ESep, EVal : Expects a key / key-val separator / value
-- TSep             : Expects a key-seperator or end of table header
-- ASep             : Expects a key-seperator or end of table of arrays header
-- EOL              : Expects end of line stuff (comment, whitespace)
-- Err              : Error state
EKey, ESep, EVal, EOL, Err, TSep, ASep : TST
EKey = 1; ESep = 2; EVal = 3; EOL = 4; Err = 5; TSep = 6; ASep = 7

-- Arrays and Inline Tabls:
-- ANew, AVal, ACom : New array / array after value / array after comma
ANew, AVal, ACom, TVal, TCom, TNew : TST
ANew = 8; AVal = 9; ACom = 10; TVal = 11; TCom = 12; TNew = 19

-- Strings
QKey, LKey, QStr, LStr, MLQStr, MLLStr : TST
QKey = 13; LKey = 14; QStr = 15; MLQStr = 16; LStr = 17; MLLStr = 18


public export
0 TSTCK : Type -> Type
TSTCK = Stack TomlParseError TStack TSz

--------------------------------------------------------------------------------
-- Tables and Values
--------------------------------------------------------------------------------

addTreeVal : TreeTable -> SnocList Key -> TomlValue -> Either TErr TreeTable
addTreeVal t sk tv =
  case vview t (sk <>> []) of
    Left x                 => Left x
    Right (VT v t k New,_) => Right $ reduceT Def (insert k.key (TV tv) t) v
    Right (v,_)            => Left $ exists [] v (TTbl empty)

addInlineVal : TomlTable -> SnocList Key -> TomlValue -> Either TErr TomlTable
addInlineVal t sk tv =
  case iview VR t (sk <>> []) of
    Left x               => Left x
    Right (VT v t k New) => Right $ reduceI (insert k.key tv t) v
    Right v              => Left $ exists [] v (TTbl empty)

parameters {auto sk : TSTCK q}

  addkey : KeyType -> Bounded String -> F1 q TST
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
    bs <- tokenBounds (length s)
    addkey Plain (B s bs)

  escape : TST -> ByteString -> F1 q TST
  escape res bs =
   let hex := cast {to = Bits32} $ hexadecimal (drop 2 bs)
    in case has unicode hex && not (has surrogate hex) of
         True  => inccol (size bs) >> pushBits32 res hex
         False => unexpected [] sk >>= flip failWith Err

  end : TST -> Either TErr TStack -> F1 q TST
  end x (Left y)  = failWith y Err
  end x (Right y) = putStackAs y x

  onval : TomlValue -> TStack -> F1 q TST
  onval v (STop x sk t) = end EOL  $ STop x [<] <$> addTreeVal t sk v
  onval v (VArr x sv)   = end AVal $ Right (VArr x (sv:<v))
  onval v (VTbl x sk t) = end TVal $ VTbl x [<] <$> addInlineVal t sk v
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
      VTbl x sk t => onval (TTbl t) x
      s           => end Err (Right s)

  qstr : String -> F1 q TST
  qstr s = getStack >>= onval (TStr s)

%inline
val : a -> (ByteString -> TomlValue) -> (a, Step q TSz TSTCK)
val x f = goBS x $ \bs => getStack >>= onval (f bs)

%inline
val' : a -> TomlValue -> (a, Step q TSz TSTCK)
val' x = val x . const

--------------------------------------------------------------------------------
-- Lexer Steps
--------------------------------------------------------------------------------

tomlSpaced : TST -> Steps q TSz TSTCK -> DFA q TSz TSTCK
tomlSpaced res ss = dfa $ conv' (plus wschar) res :: ss

tomlIgnore : TST -> TST -> Steps q TSz TSTCK -> DFA q TSz TSTCK
tomlIgnore res nl ss =
  tomlSpaced res $ [read' comment res, newline' newline nl] ++ ss

keySteps : Steps q TSz TSTCK
keySteps =
  [ goStr unquotedKey onkey
  , copen' '\'' LKey
  , copen' '"'  QKey
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
  , val fullDate  (TTime . ATLocalDate . readLocalDate)
  , val (fullDate >> opt ' ')  (TTime . ATLocalDate . readLocalDate . trim)
  , val localTime (TTime . ATLocalTime . readLocalTime)
  , val localDateTime (TTime . ATLocalDateTime . readLocalDateTime)
  , val offsetDateTime (TTime . ATOffsetDateTime . readOffsetDateTime)

  -- Nested Values
  , copen '[' openArray
  , copen '{' openInlineTable

  -- Strings
  , copen' '"'  QStr
  , copen' '\'' LStr
  , copen' #"""""# MLQStr
  , go (#"""""# >> newline) (pushPosition >> incline 1 >> pure MLQStr)
  , copen' "'''" MLLStr
  , go ("'''" >> newline) (pushPosition >> incline 1 >> pure MLLStr)
  , val' #""""# (TStr "")
  , val' #"''"# (TStr "")
  ]

escapes : TST -> Steps q TSz TSTCK
escapes res =
    [ read basicUnescaped (pushStr res)
    , cexpr #"\""# (pushStr res "\"")
    , cexpr #"\\"# (pushStr res "\\")
    , cexpr #"\b"# (pushStr res "\b")
    , cexpr #"\e"# (pushStr res "\e")
    , cexpr #"\f"# (pushStr res "\f")
    , cexpr #"\n"# (pushStr res "\n")
    , cexpr #"\r"# (pushStr res "\r")
    , cexpr #"\t"# (pushStr res "\t")
    , goBS ("\\u" >> repeat 4 hexdigit) (escape res)
    , goBS ("\\U" >> repeat 8 hexdigit) (escape res)
    ]

mlqDFA : DFA q TSz TSTCK
mlqDFA =
  dfa $
    [ ccloseStr #"""""# qstr
    , cclose #""""""# (pushStr' "\"" >> getStr >>= qstr)
    , cclose #"""""""# (pushStr' "\"\"" >> getStr >>= qstr)
    , cexpr #"""# (pushStr MLQStr "\"")
    , cexpr #""""# (pushStr MLQStr "\"\"")
    , newline newline (pushStr MLQStr "\n")
    , multiline' mlbEscapedNL MLQStr
    ] ++ escapes MLQStr

mllDFA : DFA q TSz TSTCK
mllDFA =
  dfa $
    [ ccloseStr "'''" qstr
    , cclose "''''" (pushStr' "'" >> getStr >>= qstr)
    , cclose "'''''" (pushStr' "''" >> getStr >>= qstr)
    , cexpr "'" (pushStr MLLStr "'")
    , cexpr "''" (pushStr MLLStr "''")
    , newline newline (pushStr MLLStr "\n")
    , read literalChars (pushStr MLLStr)
    ]

--------------------------------------------------------------------------------
-- State Transitions
--------------------------------------------------------------------------------

tomlTrans : Lex1 q TSz TSTCK
tomlTrans =
  lex1
    [ E Ini  $ tomlIgnore Ini Ini (keySteps ++ [copen '[' openStdTable, copen "[[" openArrayTable])
    , E ESep $ tomlSpaced ESep [cexpr' '.' EKey, cexpr' '=' EVal]
    , E TSep $ tomlSpaced TSep [cexpr' '.' EKey, cclose ']' close]
    , E ASep $ tomlSpaced ASep [cexpr' '.' EKey, cclose "]]" close]
    , E EKey $ tomlSpaced EKey keySteps
    , E EVal $ tomlSpaced EVal valSteps
    , E ANew $ tomlIgnore ANew ANew (cclose ']' close :: valSteps)
    , E AVal $ tomlIgnore AVal AVal [cclose ']' close, cexpr' ',' ACom]
    , E ACom $ tomlIgnore ACom ACom (cclose ']' close :: valSteps)
    , E QKey $ dfa $ ccloseBoundedStr '"' (addkey Quoted) :: escapes QKey
    , E LKey $ dfa [ccloseBoundedStr '\'' (addkey Plain), read literalChars (pushStr LKey)]
    , E QStr $ dfa $ ccloseStr '"' qstr :: escapes QStr
    , E LStr $ dfa [ccloseStr '\'' qstr, read literalChars (pushStr LStr)]
    , E MLQStr mlqDFA
    , E MLLStr mllDFA
    , E TVal $ tomlSpaced TVal [cexpr' ',' TCom, cclose '}' close]
    , E TNew $ tomlSpaced TNew (cclose '}' close :: keySteps)
    , E TCom $ tomlSpaced TCom keySteps
    , E EOL  $ tomlIgnore EOL Ini []
    ]

tomlErr : Arr32 TSz (TSTCK q -> F1 q TErr)
tomlErr =
  arr32 TSz (unexpected [])
    [ E ANew $ unclosedIfEOI "[" []
    , E AVal $ unclosedIfEOI "[" [",", "]"]
    , E ACom $ unclosedIfEOI "[" []
    , E TVal $ unclosedIfEOI "{" [",", "}"]
    , E TCom $ unclosedIfEOI "{" []
    ]

tomlEOI : TST -> TSTCK q -> F1 q (Either TErr TomlTable)
tomlEOI st sk =
  case st == Ini || st == EOL of
    False => arrFail TSTCK tomlErr st sk
    True  => getStack >>= pure . toTable

export
toml : P1 q TErr TSz TSTCK TomlTable
toml = P Ini (init empty) tomlTrans (\x => (Nothing #)) tomlErr tomlEOI

test : String -> IO ()
test s =
  case parseString toml Virtual s of
    Right v => printLn v
    Left  x => putStrLn "\{x}"

-- 222 LOC

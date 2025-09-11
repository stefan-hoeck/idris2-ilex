module Text.TOML.Parser

import Data.SortedMap
import Data.Linear.Ref1
import Text.ILex
import Text.TOML.Lexer
import Text.TOML.Types
import Syntax.T1

%hide Data.Linear.(.)
%default total
--------------------------------------------------------------------------------
-- States
--------------------------------------------------------------------------------

public export
TSz : Bits32
TSz = 13

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
ANew, AVal, ACom, TVal, TCom : TST
ANew = 8; AVal = 9; ACom = 10; TVal = 11; TCom = 12

public export
0 TSTCK : Type -> Type
TSTCK = Stack TomlParseError TStack TSz

--------------------------------------------------------------------------------
-- Spaces
--------------------------------------------------------------------------------

tomlSpaced : TST -> Steps q TSz TSTCK -> DFA q TSz TSTCK
tomlSpaced res ss = dfa $ (plus wschar, spaces res) :: ss

tomlIgnore : TST -> Steps q TSz TSTCK -> DFA q TSz TSTCK
tomlIgnore res ss =
  tomlSpaced res $ [(comment, lineComment res), (newline, newline Ini)] ++ ss

--------------------------------------------------------------------------------
-- Keys
--------------------------------------------------------------------------------

keyString : KeyType -> ByteString -> (String,Nat)
keyString Plain bs = (toString bs, size bs)
keyString _     bs = let s := unlit bs in (s, length s + 2)

onkey : KeyType -> (sk : TSTCK q) => ByteString -> F1 q TST
onkey tpe bs = T1.do
  p  <- getPosition
  let (s,n)  := keyString tpe bs
      k      := KT s tpe (BS p $ incCol n p)
  inccol n
  getStack >>= \case
    STbl x ks   => putStackAs (STbl x $ ks:<k) TSep
    SArr x ks   => putStackAs (SArr x $ ks:<k) ASep
    STop x ks t => putStackAs (STop x (ks:<k) t) ESep
    VTbl x ks t => putStackAs (VTbl x (ks:<k) t) ESep
    VArr x sv   => putStackAs (VArr x sv) Err

keySteps : Steps q TSz TSTCK
keySteps =
  [ (unquotedKey, rd $ onkey Plain)
  , (literalString, rd $ onkey Literal)
  ]

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------

vexists : TableType -> TView -> TErr
vexists tt v         =
  case v of
    Arr {} => exists [] v (TTbls [<])
    _      => exists [] v (TTbl tt empty)

addVal : TableType -> TomlTable -> SnocList Key -> TomlValue -> Either TErr TomlTable
addVal tt t sk tv =
  case view tt Root t (sk <>> []) of
    Left x            => Left x
    Right (New v t k) => Right $ reduceT tt (insert k.key tv t) v
    Right v           => Left $ vexists tt v

parameters {auto sk : TSTCK q}
  end : TST -> Either TErr TStack -> F1 q TST
  end x (Left y)  = failWith y Err
  end x (Right y) = putStackAs y x

  onval : TomlValue -> TStack -> F1 q TST
  onval v (STop x sk t) = end EOL  $ STop x [<] <$> addVal Table t sk v
  onval v (VArr x sv)   = end AVal $ Right (VArr x (sv:<v))
  onval v (VTbl x sk t) = end TVal $ VTbl x [<] <$> addVal Inline t sk v
  onval v s             = end Err (Right s)

  openStdTable : F1 q TST
  openStdTable = getStack >>= \s => putStackAs (STbl (toRoot s) [<]) EKey

  openArrayTable : F1 q TST
  openArrayTable = getStack >>= \s => putStackAs (SArr (toRoot s) [<]) EKey

  openArray : F1 q TST
  openArray = getStack >>= \s => putStackAs (VArr s [<]) ANew

  openInlineTable : F1 q TST
  openInlineTable = getStack >>= \s => putStackAs (VTbl s [<] empty) EKey

  close : F1 q TST
  close =
    getStack >>= \case
      STbl t sk =>
        case view Table Root t (sk <>> []) of
          Right v@(New {}) => putStackAs (STop v [<] empty) EOL
          Right v          => failWith (vexists Table v) Err
          Left  x          => failWith x Err
      SArr t sk =>
        case view Table Root t (sk <>> []) of
          Right (New v t k)       => putStackAs (STop (Arr v t k [<] empty) [<] empty) EOL
          Right (Arr v t k st t2) => putStackAs (STop (Arr v t k (st:<t2) empty) [<] empty) EOL
          Right v                 => failWith (vexists Table v) Err
          Left  x                 => failWith x Err
      VArr x sx   => onval (TArr sx) x
      VTbl x sk t => onval (TTbl Inline t) x
      s           => end Err (Right s)

%inline
val : a -> (ByteString -> TomlValue) -> (a, Step q TSz TSTCK)
val x f = (x, rd $ \bs => getStack >>= onval (f bs))

%inline
val' : a -> TomlValue -> (a, Step q TSz TSTCK)
val' x = val x . const

valDFA : DFA q TSz TSTCK
valDFA =
  tomlSpaced EVal
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
    , val localTime (TTime . ATLocalTime . readLocalTime)
    , val localDateTime (TTime . ATLocalDateTime . readLocalDateTime)
    , val offsetDateTime (TTime . ATOffsetDateTime . readOffsetDateTime)

    -- Nested Values
    , copen '[' openArray
    , copen '{' openInlineTable
    ]

--------------------------------------------------------------------------------
-- State Transitions
--------------------------------------------------------------------------------

tomlTrans : Lex1 q TSz TSTCK
tomlTrans =
  lex1
    [ E Ini  $ tomlIgnore Ini (keySteps ++ [copen '[' openStdTable, copen "[[" openArrayTable])
    , E ESep $ tomlSpaced ESep [cexpr' '.' EKey, cexpr' '=' EVal]
    , E TSep $ tomlSpaced TSep [cexpr' '.' EKey, cclose ']' close]
    , E ASep $ tomlSpaced ASep [cexpr' '.' EKey, cclose "]]" close]
    , E EKey $ tomlSpaced EKey keySteps
    , E EVal valDFA
    , E EOL  $ tomlIgnore EOL []
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
    True  => getStack >>= pure . Right . toRoot

export
toml : P1 q TErr TSz TSTCK TomlTable
toml = P Ini (init empty) tomlTrans (\x => (Nothing #)) tomlErr tomlEOI

test : String -> IO ()
test s =
  case parseString toml Virtual s of
    Right v => printLn v
    Left  x => putStrLn "\{x}"

-- 222 LOC

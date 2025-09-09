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
TSz = 10

public export
TST : Type
TST = Index TSz

-- Keys and utilities:
-- EKey, ESep, EVal : Expects a toplevel key / separator / value
-- EOL              : Expects end of line stuff (comment, whitespace)
-- Err              : Error state
EKey, ESep, EVal, EOL, Err : TST
EKey = 1; ESep = 2; EVal = 3; EOL = 4; Err = 5

-- Arrays:
-- ANew, AVal, ACom : New array / array after value / array after comma
ANew, AVal, ACom : TST
ANew = 6; AVal = 7; ACom = 8

public export
0 TSTCK : Type -> Type
TSTCK = Stack TomlParseError TStack TSz

--------------------------------------------------------------------------------
-- Spaces
--------------------------------------------------------------------------------

tomlIgnore : TST -> Steps q TSz TSTCK
tomlIgnore res =
  [ (plus wschar, spaces res)
  , (comment, lineComment res)
  , (newline, newline Ini)
  ]

--------------------------------------------------------------------------------
-- Keys
--------------------------------------------------------------------------------

err : BoundedErr TomlParseError -> (sk : TSTCK q) => F1 q TST
err x = writeAs sk.err (Just x) Err

-- keyString : KeyType -> ByteString -> (String,Nat)
-- keyString Plain bs = (toString bs, size bs)
-- keyString _     bs = let s := unlit bs in (s, length s + 2)
--
-- onkey : KeyType -> (sk : TSTCK q) => ByteString -> F1 q TST
-- onkey tpe bs = T1.do
--   p  <- getPosition
--   s1 <- read1 sk.stck
--   let (s,n) := keyString tpe bs
--       k     := KT s tpe (BS p $ incCol n p)
--       Right s2 := follow s1 k | Left x => err x
--   inccol n
--   writeAs sk.stck s2 ISep
--
-- keySteps : Steps q TSz TSTCK
-- keySteps =
--   [ (unquotedKey, rd $ onkey Plain)
--   , (literalString, rd $ onkey Literal)
--   , copen' '"' QKey
--   ]
--
-- afterKey : DFA q TSz TSTCK
--
-- --------------------------------------------------------------------------------
-- -- Values
-- --------------------------------------------------------------------------------
--
-- onval : (sk : TSTCK q) => TomlValue -> F1 q TST
-- onval v = T1.do
--   p <- read1 sk.stck
--   Right p2 <- pure (addVal v p) | Left x => err x
--   writeAs sk.stck p2 EOL
--
-- %inline
-- val : a -> (ByteString -> TomlValue) -> (a, Step q TSz TSTCK)
-- val x f = (x, rd $ \bs => onval (f bs))
--
-- %inline
-- val' : a -> TomlValue -> (a, Step q TSz TSTCK)
-- val' x = val x . const
--
-- valDFA : DFA q TSz TSTCK
-- valDFA =
--   dfa
--     [ val' "true"  (TBool True)
--     , val' "false" (TBool False)
--
--     -- integers
--     , val  decInt  (TInt . readDecInt)
--     , val  binInt  (TInt . binarySep . drop 2)
--     , val  octInt  (TInt . octalSep underscore . drop 2)
--     , val  hexInt  (TInt . hexadecimalSep underscore . drop 2)
--
--     -- floats
--     , val' nan     (TDbl NaN)
--     , val' posInf  (TDbl $ Infty Plus)
--     , val' "-inf"  (TDbl $ Infty Minus)
--     , val float    (TDbl . readFloat)
--
--     -- Date and Time
--     , val fullDate  (TTime . ATLocalDate . readLocalDate)
--     , val localTime (TTime . ATLocalTime . readLocalTime)
--     , val localDateTime (TTime . ATLocalDateTime . readLocalDateTime)
--     , val offsetDateTime (TTime . ATOffsetDateTime . readOffsetDateTime)
--     ]

--------------------------------------------------------------------------------
-- State Transitions
--------------------------------------------------------------------------------

tomlTrans : Lex1 q TSz TSTCK
-- tomlTrans =
--   lex1
--     [ E Ini  $ dfa (tomlIgnore Ini ++ keySteps) -- ++ tableOrArray
--     , E ISep $ dfa [conv' dotSep IKey, conv' keyvalSep IVal]
--     , E IKey $ dfa keySteps
--     , E IVal valDFA
--     , E EOL  $ dfa (tomlIgnore EOL)
--     ]

tomlErr : Arr32 TSz (TSTCK q -> F1 q TErr)
-- tomlErr =
--   arr32 TSz (unexpected [])
--     [ E ANew $ unclosedIfEOI "[" []
--     , E AVal $ unclosedIfEOI "[" [",", "]"]
--     , E ACom $ unclosedIfEOI "[" []
--     , E QKey $ unclosedIfEOI "\"" []
--     ]

tomlEOI : TST -> TSTCK q -> F1 q (Either TErr TomlTable)
-- tomlEOI st sk =
--   case st == Ini || st == EOL of
--     False => arrFail TSTCK tomlErr st sk
--     True  => read1 sk.stck >>= pure . Right . toRoot

export
toml : P1 q TErr TSz TSTCK TomlTable
toml = P Ini (init $ Root empty) tomlTrans (\x => (Nothing #)) tomlErr tomlEOI

test : String -> IO ()
test s =
  case parseString toml Virtual s of
    Right v => printLn v
    Left  x => putStrLn "\{x}"

-- 222 LOC

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
-- Parser Stack
--------------------------------------------------------------------------------

data Part : Type where
  Top    : TomlTable -> Part
  Tbl    : Path -> TomlTable -> Part
  Key    : (p : Part) -> Path -> Part
  Arr    : (p : Part) -> SnocList TomlValue -> Part

export
record TSTCK q where
  constructor T
  line   : Ref q Nat
  col    : Ref q Nat
  bounds : Ref q (SnocList Bounds)
  part   : Ref q Part
  keys   : Ref q (SnocList Key)
  strs   : Ref q (SnocList String)

export %inline
LC TSTCK where
  line   = TSTCK.line
  col    = TSTCK.col
  bounds = TSTCK.bounds

init : F1 q (TSTCK q)
init = T1.do
  l <- ref1 Z
  c <- ref1 Z
  b <- ref1 [<]
  p <- ref1 (Top empty)
  k <- ref1 [<]
  s <- ref1 [<]
  pure (T l c b p k s)

--------------------------------------------------------------------------------
-- States
--------------------------------------------------------------------------------

public export
TSz : Bits32
TSz = 10

public export
TST : Type
TST = Index TSz

AfterKey, AfterSep, QKey, ANew, AVal, ACom, AfterVal : TST
AfterKey = 1; AfterSep = 2; BeforeKey = 3
QKey     = 4
ANew     = 5; AVal = 6; ACom = 7
AfterVal = 8

table : TomlTable -> Part -> Part
table t (Top _)    = Top t
table t (Tbl p _)  = Tbl p t
table t p          = p

value : TomlValue -> Part -> (Part,TST)
value v (Key p x)    = (table (unwind v x) p, AfterVal)
value v (Arr p sx)   = (Arr p (sx:<v), AVal)
value v p            = (p, Ini)

key : List Key -> Part -> Either TErr Part
key ks p@(Top t)   = Key p <$> valuePath Root ks t
key ks p@(Tbl _ t) = Key p <$> valuePath Root ks t
key _  p           = Right p

--------------------------------------------------------------------------------
-- Spaces
--------------------------------------------------------------------------------

tomlIgnore : TST -> Steps1 q e TSz TSTCK
tomlIgnore res =
  [ (plus wschar, spaces res)
  , (comment, lineComment res)
  , (newline, newline Ini)
  ]

--------------------------------------------------------------------------------
-- Keys
--------------------------------------------------------------------------------

keyString : KeyType -> ByteString -> (String,Nat)
keyString Plain bs = (toString bs, size bs)
keyString _     bs = let s := unlit bs in (s, length s + 2)

onkey : KeyType -> TSTCK q -> ByteString -> F1 q TST
onkey tpe sk bs = T1.do
  ps <- currentPos sk
  let (s,n) := keyString tpe bs
  push1 sk.keys () (KT s tpe $ BS ps ({column $= (+n)} ps))
  incCols n sk AfterKey

keySteps : TST -> Steps1 q TErr TSz TSTCK
keySteps =
  [ (unquotedKey, rd $ onkey Plain)
  , (literalString, rd $ onkey Literal)
  , copen '"' (const TSTCK QKey)
  ]

exprSteps : Steps1 q TErr TSz TSTCK
-- exprSteps =


--
-- setKey : TSTCK q -> ByteString -> F1 q (Either TErr TST)
-- setKey sk bs = T1.do
--   ks <- getList sk.keys
--   p  <- read1 sk.part
--   let Right p2 := key ks p | Left err => pure (Left err)
--   write1 sk.part p2
--   incCols bs.size sk (Right AfterSep)
--
-- afterKey : DFA (Step1 q TErr TSz TSTCK)
-- afterKey = dfa Err [state dotSep Ini, (keyvalSep, prs setKey)]
--
-- --------------------------------------------------------------------------------
-- -- Values
-- --------------------------------------------------------------------------------
--
-- onval : TomlValue -> TSTCK q -> F1 q (Either TErr TST)
-- onval v sk = T1.do
--   p <- read1 sk.part
--   let (p2,res) := value v p
--   writeAs sk.part p2 (Right res)
--
-- %inline
-- val : a -> (ByteString -> TomlValue) -> (a, Step1 q TErr TSz TSTCK)
-- val x f = (x, Prs $ \(B sk bs t) => onval (f bs) sk t)
--
-- %inline
-- val' : a -> TomlValue -> (a, Step1 q TErr TSz TSTCK)
-- val' x = val x . const
--
-- valDFA : DFA (Step1 q TErr TSz TSTCK)
-- valDFA =
--   dfa Err
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
--
-- --------------------------------------------------------------------------------
-- -- State Transitions
-- --------------------------------------------------------------------------------
--
-- tomlTrans : Lex1 q TErr TSz TSTCK
-- tomlTrans =
--   lex1
--     [ E Ini      keyDFA
--     , E AfterKey afterKey
--     , E AfterSep valDFA
--     , E AfterVal (tomlIgnore AfterVal [])
--     ]

-- 222 LOC

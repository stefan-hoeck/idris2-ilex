module Text.TOML.Parser

import Data.SortedMap
import Data.Linear.Ref1
import Text.ILex
import Text.TOML.Lexer
import Text.TOML.Types
import Syntax.T1

%default total

--------------------------------------------------------------------------------
-- Parser Stack
--------------------------------------------------------------------------------

data Part : Type where
  Top : Part
  PA  : (p : Part) -> SnocList TomlValue -> Part
  PT  : (p : Part) -> SnocList (String,TomlValue) -> Part
  PL  : (p : Part) -> SnocList (String,TomlValue) -> String -> Part

export
record TSTCK q where
  constructor T
  line   : Ref q Nat
  col    : Ref q Nat
  bounds : Ref q (SnocList Bounds)
  part   : Ref q Part
  table  : Ref q TomlTable
  keys   : Ref q (SnocList String)
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
  p <- ref1 Top
  t <- ref1 SortedMap.empty
  k <- ref1 [<]
  s <- ref1 [<]
  pure (T l c b p t k s)

--------------------------------------------------------------------------------
-- States
--------------------------------------------------------------------------------

public export
TSz : Bits32
TSz = 10

public export
TST : Type
TST = Index TSz

AfterKey, BeforeVal, QKey, LKey : TST
AfterKey  = 1
BeforeVal = 2
QKey      = 3
LKey      = 4

--------------------------------------------------------------------------------
-- Keys
--------------------------------------------------------------------------------

keyDFA : TST -> DFA (Step1 q e TSz TSTCK)
keyDFA after =
  dfa Err
    [ read unquotedKey ?foooo
    , read literalString ?baaar
    , copen '"' (const TSTCK QKey)
    ]

afterKey : DFA (Step1 q e TSz TSTCK)
afterKey = dfa Err [ state dotSep Ini, state keyvalSep BeforeVal]

beforeVal : DFA (Step1 q e TSz TSTCK)

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------

onVal : TomlValue -> Step1 q e TSz TSTCK

val : DFA (Step1 q e TSz TSTCK)
val =
  dfa Err
    [ ("true",  onVal $ TBool True)
    , ("false", onVal $ TBool False)
    , (nan    , onVal $ TDbl NaN)
    , (posInf , onVal $ TDbl $ Infty Plus)
    , ("-inf" , onVal $ TDbl $ Infty Minus)
    ]

--------------------------------------------------------------------------------
-- State Transitions
--------------------------------------------------------------------------------

tomlTrans : Lex1 q e TSz TSTCK
tomlTrans =
  lex1
    [ E Ini       $ keyDFA AfterKey
    , E AfterKey  afterKey
    , E BeforeVal beforeVal
    ]

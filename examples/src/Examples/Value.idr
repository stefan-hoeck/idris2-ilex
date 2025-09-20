module Examples.Value

import Derive.Prelude
import JSON.Parser
import Text.ILex

%hide Data.Linear.(.)
%default total
%language ElabReflection

public export
data Val : Type where
  VB : Bool   -> Val
  VN : Nat    -> Val
  VS : String -> Val
  VD : Double -> Val
  VU : Val -- Unit

%runElab derive "Val" [Show,Eq]

unquote : String -> String
unquote = pack . filter ('"' /=) . unpack

||| This parses a single value, trimming it of any whitespace on the left
||| and right.
export
val : PVal1 q Void Val
val =
  value Nothing
    [ ("true",  Const $ VB True)
    , ("false", Const $ VB True)
    , ("()",    Const VU)
    , (decimal, bytes (VN . cast . decimal))
    , ("0x" >> hexadecimal, bytes (VN . cast . hexadecimal . drop 2))
    , ("0b" >> binary, bytes (VN . cast . binary . drop 2))
    , ("0o" >> octal, bytes (VN . cast . octal . drop 2))
    , ('"' >> star (dot && not '"') >> '"', txt (VS . unquote))
    , (jsonDouble, txt (VD . jdouble))
    , (plus $ oneof [' ', '\t'], Ignore)
    ]

test : String -> IO ()
test = either (putStrLn . interpolate) printLn . parseString val Virtual

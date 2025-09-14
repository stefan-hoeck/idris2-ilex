module Manual

import Value

%default total

prop_empty : Property
prop_empty = property1 $ do
  testTOML "\n"   === tbl []
  testTOML "\r\n" === tbl []
  testTOML ""     === tbl []
  testTOML " "    === tbl []
  testTOML "\t"   === tbl []

export
props : Group
props =
  MkGroup "Text.TOML.Lexer.Manual"
    [ ("prop_empty", prop_empty)
    ]

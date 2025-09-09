module Value

import public Data.SortedMap as SM
import public Text.ILex
import public Text.TOML.Parser
import public Text.TOML.Types
import public Hedgehog

%default total

export
testTOML : String -> Either (ParseError TomlParseError) TomlTable
testTOML = parseString toml Virtual

export
tbl : List (String, TomlValue) -> Either a TomlTable
tbl = Right . SM.fromList

prop_bool : Property
prop_bool = property1 $ do
  testTOML "foo = true"  === tbl [("foo", TBool True)]
  testTOML "foo = false" === tbl [("foo", TBool False)]

prop_integer : Property
prop_integer =
  property $ do
    n <- forAll (integer $ linear (-1000) 1000)
    testTOML "foo = \{show n}" === tbl [("foo", TInt n)]

export
props : Group
props =
  MkGroup "Text.TOML.Lexer"
    [ ("prop_bool", prop_bool)
    , ("prop_integer", prop_integer)
    ]

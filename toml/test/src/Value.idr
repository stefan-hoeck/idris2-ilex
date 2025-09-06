module Value

import Text.TOML.Lexer
import Text.TOML.Types
import Hedgehog

%default total

export
props : Group
props =
  MkGroup "Text.TOML.Lexer"
    [
    ]

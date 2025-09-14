module Main

import Value
import Manual
import Spec
import Hedgehog

%default total

covering
main : IO ()
main =
  spec >>
  test
    [ Value.props
    , Manual.props
    ]

module Main

import Value
import Manual
import Hedgehog

%default total

main : IO ()
main =
  test
    [ Value.props
    , Manual.props
    ]

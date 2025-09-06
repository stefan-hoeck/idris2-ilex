module Main

import Value
import Hedgehog

%default total

main : IO ()
main =
  test
    [ Value.props
    ]

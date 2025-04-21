module Main

import Hedgehog
import Range

%default total

main : IO ()
main =
  test
    [ Range.props
    ]

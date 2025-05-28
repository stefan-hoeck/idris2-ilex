module Main

import Hedgehog
import FC
import Range
import Runner
import Set

%default total

main : IO ()
main =
  test
    [ Range.props
    , Set.props
    , FC.props
    , Runner.props
    ]

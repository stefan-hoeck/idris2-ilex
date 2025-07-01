module Main

import Context
import FC
import Hedgehog
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
    , Context.props
    ]

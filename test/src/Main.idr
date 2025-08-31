module Main

import Context
import FC
import Hedgehog
import Repeat
import Range
import Runner
import Set
import Unicode

%default total

main : IO ()
main =
  test
    [ Range.props
    , Repeat.props
    , Set.props
    , FC.props
    , Runner.props
    , Context.props
    , Unicode.props
    ]

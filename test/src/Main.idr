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
    [ Runner.props
    , FC.props
    , Set.props
    , Unicode.props
    , Context.props
    , Range.props
    , Repeat.props
    ]

module Main

import Context
import FC
import Hedgehog
import Range
import Repeat
import Runner
import Set
import Stream
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
    , Stream.props
    ]

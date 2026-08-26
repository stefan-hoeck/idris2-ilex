module Main

import ByteRange
import Hedgehog

%default total

main : IO ()
main = test [ByteRange.props]

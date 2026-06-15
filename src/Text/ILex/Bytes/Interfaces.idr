module Text.ILex.Bytes.Interfaces

import Data.Linear.Ref1
import Syntax.T1
import public Text.ByteBounds
import public Text.ILex.Parser

%default total

||| An interface for mutable parser stacks `s` that allows us to keep
||| track of the current byte position.
public export
interface HasBytePos (0 s : Type -> Type) where
  constructor MkHBP
  pos       : s q -> Ref q BytePos
  positions : s q -> Ref q (SnocList BytePos)

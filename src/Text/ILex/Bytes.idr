module Text.ILex.Bytes

import Data.Buffer
import public Text.ILex.Runner
import public Text.ILex.Bytes.Interfaces
import public Text.ILex.Bytes.Stack

%default total

||| Like `run` but fails with a proper parse error
||| including error bounds and highlighting of
||| the section where an error occurred.
export %inline
parseBB :
     {n : _}
  -> Parser1 (BBErr e) a
  -> Origin
  -> IBuffer n
  -> Either (ParseError e) a
parseBB l o buf = mapFst (toParseError o (toString buf 0 n)) (run l buf)

||| Like `parse` but processes a UTF-8 string instead.
export %inline
parseStringBB :
     Parser1 (BBErr e) a
  -> Origin
  -> String
  -> Either (ParseError e) a
parseStringBB l o s = parseBB l o (fromString s)

||| Like `parse` but processes a `ByteString` instead.
export %inline
parseBytesBB :
     Parser1 (BBErr e) a
  -> Origin
  -> ByteString
  -> Either (ParseError e) a
parseBytesBB l o bs = mapFst (toParseError o (toString bs)) (runBytes l bs)

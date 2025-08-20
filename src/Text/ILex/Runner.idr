-- TODO: Optimize `Txt` cases
module Text.ILex.Runner

import public Data.ByteString
import public Data.Linear.Token
import public Data.Vect
import public Text.ILex.Bounds
import public Text.ILex.Error
import public Text.ILex.FC
import public Text.ILex.Lexer

import Control.WellFounded
import Data.Buffer
import Data.Buffer.Core
import Data.Buffer.Indexed
import Text.ILex.Internal.Runner
import Text.ILex.Util

%default total

||| Result type of lexing a self-contained sequence of bytes.
public export
0 ParseRes : (e,t,a : Type) -> Type
ParseRes e t a = Either (ParseError t e) a

parseFrom :
     {n      : Nat}
  -> (o      : Origin)
  -> (l      : Parser e t a)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> ParseRes e t a

||| Tries to lex a whole byte vector into a list of bounded
||| tokens.
export %inline
parse : {n : _} -> Origin -> Parser e t a -> IBuffer n -> ParseRes e t a
parse o l buf = parseFrom o l n buf

||| Like `lex` but processes a UTF-8 string instead.
export %inline
parseString : Origin -> Parser e t a -> String -> ParseRes e t a
parseString o l s = parse o l (fromString s)

||| Like `lex` but processes a `ByteString` instead.
export
parseBytes : Origin -> Parser e t a -> ByteString -> ParseRes e t a
parseBytes o l (BS s $ BV buf off lte) =
  parseFrom o l s {x = offsetToIx off} (take (off+s) buf)

--------------------------------------------------------------------------------
-- Lexer run loop
--------------------------------------------------------------------------------

parameters (p   : Parser e t a)
           (buf : IBuffer n)

  loop :
       (st           : p.state)
    -> (pos,line,col : Nat)
    -> {auto x       : Ix pos n}
    -> (0 acc        : SizeAccessible pos)
    -> Either (Bounded $ InnerError t e) a
  loop st 0     l c _            = p.eoi (atPos $ P l c) st
  loop st (S k) l c (Access rec) =
    case step (p.lex st) buf k l c of
      R end l2 c2 @{_} @{lt} tok =>
        case apply p st tok (toBS buf (S k) end) (BS (P l c) (P l2 c2)) of
          Right x => loop x end l2 c2 (rec _ lt)
          Left  x => Left x
      E end y => Left $ B y $ BS (P l c) end

parseFrom o p pos buf =
  case loop p buf p.init pos 0 0 (sizeAccessible pos) of
    Left (B x bs) => Left $ PE o bs (fromIBuffer buf) x
    Right v       => Right v

module Text.ILex.Error

import Derive.Prelude
import Data.ByteString

import Text.ILex.Bounds
import Text.ILex.Char.UTF8
import Text.ILex.FC

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Parse Errors
--------------------------------------------------------------------------------

public export
data InnerError : (token, err : Type) -> Type where
  ||| A custom error for the current parsing topic
  Custom       : (err : e) -> InnerError t e

  ||| Unexpected end of input
  EOI          : InnerError t e

  ||| Expected the given token but got something else.
  Expected     : t -> InnerError t e

  ||| Got more input that we expected
  ExpectedEOI  : InnerError t e

  ||| An unclosed opening token
  Unclosed     : t -> InnerError t e

  ||| Got an unexpected token
  Unexpected   : t -> InnerError t e

  ||| Got an unknown or invalid token
  Byte         : Bits8 -> InnerError t e

%runElab derive "InnerError" [Show,Eq]

public export
Bifunctor InnerError where
  bimap f g (Custom err)   = Custom $ g err
  bimap f g EOI            = EOI
  bimap f g (Expected x)   = Expected $ f x
  bimap f g ExpectedEOI    = ExpectedEOI
  bimap f g (Unclosed x)   = Unclosed $ f x
  bimap f g (Unexpected x) = Unexpected $ f x
  bimap f g (Byte x)       = Byte x

export
Interpolation t => Interpolation e => Interpolation (InnerError t e) where
  interpolate EOI                = "Unexpected end of input"
  interpolate (Expected x)       = "Expected \{x}"
  interpolate ExpectedEOI        = "Expected end of input"
  interpolate (Unclosed x)       = "Unclosed \{x}"
  interpolate (Unexpected x)     = "Unexpected \{x}"
  interpolate (Custom err)       = interpolate err
  interpolate (Byte b)           =
    case b < 128 of
      True => case isControl b of
        True  => "Unexpected \{toHex b}"
        False => "Unexpected \{show $ cast {to = Char} b}"
      False => "Unexpected \{toHex b}"

--------------------------------------------------------------------------------
--          Identities
--------------------------------------------------------------------------------

public export
voidLeft : InnerError Void e -> InnerError t e
voidLeft EOI         = EOI
voidLeft ExpectedEOI = ExpectedEOI
voidLeft (Custom x)  = Custom x
voidLeft (Byte x)    = Byte x

public export
fromVoid : InnerError Void Void -> InnerError t e
fromVoid EOI         = EOI
fromVoid ExpectedEOI = ExpectedEOI
fromVoid (Byte x)    = Byte x

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

public export
interface FailParse (0 m : Type -> Type) (0 t,e : Type) | m where
  parseFail : Bounds -> InnerError t e -> m a

public export %inline
FailParse (Either $ Bounded $ InnerError t e) t e where
  parseFail b err = Left (B err b)

public export %inline
custom : FailParse m t e => Bounds -> e -> m a
custom b = parseFail b . Custom

public export %inline
expected : FailParse m t e => Bounds -> t -> m a
expected b = parseFail b . Expected

public export %inline
unclosed : FailParse m t e => Bounds -> t -> m a
unclosed b = parseFail b . Unclosed

public export %inline
unexpected : FailParse m t e => Bounded t -> m a
unexpected v = parseFail v.bounds (Unexpected $ v.val)

public export %inline
eoi : FailParse m t e => m a
eoi = parseFail Empty EOI

public export %inline
expectedEOI : FailParse m t e => Bounds -> m a
expectedEOI b = parseFail b ExpectedEOI

--------------------------------------------------------------------------------
--          Parse Error
--------------------------------------------------------------------------------

public export
record ParseError t e where
  constructor PE
  origin  : Origin
  bounds  : Bounds
  content : ByteString
  error   : InnerError t e

%runElab derive "ParseError" [Show,Eq]

export
Interpolation t => Interpolation e => Interpolation (ParseError t e) where
  interpolate (PE origin bounds cont err) =
    case bounds of
      Empty  => "Error in \{origin}: \{err}"
      BS s e =>
       let fc := FC origin (toPosition s cont) (toPosition e cont)
        in unlines $ "Error: \{err}" :: printFC fc (lines $ toString cont)

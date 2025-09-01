module Text.ILex.Error

import Derive.Prelude
import Data.ByteString
import Data.String

import Text.ILex.Bounds
import Text.ILex.FC
import Text.ILex.Char.UTF8

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Parse Errors
--------------------------------------------------------------------------------

public export
data InnerError : (err : Type) -> Type where
  ||| A custom error for the current parsing topic
  Custom       : (err : e) -> InnerError e

  ||| Unexpected end of input
  EOI          : InnerError e

  ||| Expected one of the given tokens but got something else.
  Expected     : List String -> String -> InnerError e

  ||| Got more input that we expected
  ExpectedEOI  : InnerError e

  ||| An unclosed opening token
  Unclosed     : String -> InnerError e

  ||| Got an unexpected token
  Unexpected   : String -> InnerError e

%runElab derive "InnerError" [Show,Eq]

public export
Functor InnerError where
  map f (Custom err)    = Custom $ f err
  map f EOI             = EOI
  map f (Expected xs x) = Expected xs x
  map f ExpectedEOI     = ExpectedEOI
  map f (Unclosed x)    = Unclosed x
  map f (Unexpected x)  = Unexpected x

quote : String -> String
quote s =
  case length s of
    1 => "'\{s}'"
    _ => "\"\{s}\""

quotes : List String -> String
quotes []        = quote ""
quotes [x]       = quote x
quotes [x,y]     = "\{quote x} or \{quote y}"
quotes (x :: xs) = go x xs
  where
    go : String -> List String -> String
    go s []        = "or \{quote s}"
    go s (y :: ys) = "\{quote s}, " ++ go y ys

export
Interpolation e => Interpolation (InnerError e) where
  interpolate EOI                = "Unexpected end of input"
  interpolate (Expected xs x)    = "Expected \{quotes xs}, but got \{quote x}"
  interpolate ExpectedEOI        = "Expected end of input"
  interpolate (Unclosed x)       = "Unclosed \{quote x}"
  interpolate (Unexpected x)     = "Unexpected \{quote x}"
  interpolate (Custom err)       = interpolate err

--------------------------------------------------------------------------------
--          Identities
--------------------------------------------------------------------------------

public export
fromVoid : InnerError Void -> InnerError e
fromVoid EOI             = EOI
fromVoid (Expected ss s) = Expected ss s
fromVoid ExpectedEOI     = ExpectedEOI
fromVoid (Unclosed s)    = Unclosed s
fromVoid (Unexpected s)  = Unexpected s

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

public export
interface FailParse (0 m : Type -> Type) (0 e : Type) | m where
  parseFail : Bounds -> InnerError e -> m a

public export %inline
FailParse (Either $ Bounded $ InnerError e) e where
  parseFail b err = Left (B err b)

public export %inline
custom : FailParse m e => Bounds -> e -> m a
custom b = parseFail b . Custom

public export %inline
expected : FailParse m e => Bounds -> List String -> String -> m a
expected b ss = parseFail b . Expected ss

public export %inline
unclosed : FailParse m e => Bounds -> String -> m a
unclosed b = parseFail b . Unclosed

public export %inline
unexpected : FailParse m e => Bounds -> String -> m a
unexpected b = parseFail b . Unexpected

public export %inline
eoi : FailParse m e => Bounds -> m a
eoi b = parseFail b EOI

public export %inline
expectedEOI : FailParse m e => Bounds -> m a
expectedEOI b = parseFail b ExpectedEOI

public export
0 BoundedErr : Type -> Type
BoundedErr = Bounded . InnerError

--------------------------------------------------------------------------------
--          Parse Error
--------------------------------------------------------------------------------

public export
record ParseError e where
  constructor PE
  origin  : Origin
  bounds  : Bounds
  content : Maybe String
  error   : InnerError e

%runElab derive "ParseError" [Show,Eq]

export
toStreamError : Origin -> Bounded (InnerError e) -> ParseError e
toStreamError o (B err bs) = PE o bs Nothing err

export
toParseError : Origin -> String -> Bounded (InnerError e) -> ParseError e
toParseError o s (B err bs) = PE o bs (Just s) err

export
Interpolation e => Interpolation (ParseError e) where
  interpolate (PE origin bounds cont err) =
    case bounds of
      Empty  => "Error in \{origin}: \{err}"
      BS s e =>
       let fc := FC origin s e
        in case cont of
             Just c  => unlines $ "Error: \{err}" :: printFC fc (lines c)
             Nothing => unlines ["Error: \{err}", interpolate fc]

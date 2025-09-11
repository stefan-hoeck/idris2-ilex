module Text.TOML.Lexer

import Data.Buffer
import Data.ByteString
import Data.List
import Data.Maybe
import Text.TOML.Types
import Text.ILex.RExp
import Text.ILex.Util

%default total

--------------------------------------------------------------------------------
-- General Character Classes
--------------------------------------------------------------------------------

export %inline
underscore : Bits8
underscore = 95

||| wschar =  %x20  ; Space
||| wschar =/ %x09  ; Horizontal tab
export
wschar : RExp True
wschar = ' ' || '\t'

||| newline =  %x0A     ; LF
||| newline =/ %x0D.0A  ; CRLF
export
newline : RExp True
newline = '\n' <|> "\r\n"

||| non-ascii = %x80-D7FF / %xE000-10FFFF
export
nonAscii : RExp True
nonAscii = range32 0x80 0xd7ff || range32 0xe000 0x10fff

||| non-eol = %x09 / %x20-7F / non-ascii
export
nonEOL : RExp True
nonEOL = '\t' || range32 0x20 0x7f || nonAscii

||| comment-start-symbol = %x23 ; #
||| comment = comment-start-symbol *non-eol
export
comment : RExp True
comment = '#' >> star nonEOL

--------------------------------------------------------------------------------
-- Strings and Keys
--------------------------------------------------------------------------------

||| unquoted-key = 1*( ALPHA / DIGIT / %x2D / %x5F ) ; A-Z / a-z / 0-9 / - / _
export
unquotedKey : RExp True
unquotedKey = plus (alphaNum || '-' || '_')

||| literal-char = %x09 / %x20-26 / %x28-7E / non-ascii
export
literalChar : RExp True
literalChar = '\t' || range32 0x20 0x26 || range32 0x28 0x7e || nonAscii

export
literalString : RExp True
literalString = '\'' >> star literalChar >> '\''

export %inline
unlit : ByteString -> String
unlit = toString . drop 1 . dropEnd 1

||| basic-unescaped = wschar / %x21 / %x23-5B / %x5D-7E / non-ascii
export
basicUnescaped : RExp True
basicUnescaped =
  wschar || '!' || range32 0x23 0x5b || range32 0x5d 0x7e || nonAscii

--------------------------------------------------------------------------------
-- Numbers
--------------------------------------------------------------------------------

mp : RExp False
mp = opt $ oneof ['-', '+']

||| dec-int = [ minus / plus ] unsigned-dec-int
||| unsigned-dec-int = DIGIT / digit1-9 1*( DIGIT / underscore DIGIT )
export
decInt : RExp True
decInt = mp >> ('0' <|> (posdigit >> star (opt '_' >> digit)))

||| bin-int = bin-prefix digit0-1 *( digit0-1 / underscore digit0-1 )
export
binInt : RExp True
binInt = "0b" >> bindigit >> star (opt '_' >> bindigit)

||| oct-int = oct-prefix digit0-7 *( digit0-7 / underscore digit0-7 )
export
octInt : RExp True
octInt = "0o" >> octdigit >> star (opt '_' >> octdigit)

||| hex-int = hex-prefix HEXDIG *( HEXDIG / underscore HEXDIG )
export
hexInt : RExp True
hexInt = "0x" >> hexdigit >> star (opt '_' >> hexdigit)

export
readDecInt : ByteString -> Integer
readDecInt    (BS 0 _)      = 0
readDecInt bs@(BS (S k) bv) =
  case bv `at` 0 of
    43 => decimalSep underscore (BS k $ tail bv) -- '+xyz'
    45 => negate $ decimalSep underscore (BS k $ tail bv) -- '-xyz'
    _  => decimalSep underscore bs -- 'xyz'

export
nan : RExp True
nan = mp >> "nan"

export
posInf : RExp True
posInf = opt '+' >> "inf"

||| float = float-int-part ( exp / frac [ exp ] )
||| float-int-part = dec-int
||| frac = decimal-point zero-prefixable-int
||| decimal-point = %x2E               ; .
||| zero-prefixable-int = DIGIT *( DIGIT / underscore DIGIT )
||| exp = "e" float-exp-part
||| float-exp-part = [ minus / plus ] zero-prefixable-int
export
float : RExp True
float = decInt >> (exp <|> (frac >> opt exp))
  where
    frac, exp, zeroPrefixableInt : RExp True
    frac              = '.' >> zeroPrefixableInt
    exp               = 'e' >> mp >> zeroPrefixableInt
    zeroPrefixableInt = digit >> star (opt '_' >> digit)

export
readFloat : ByteString -> TomlFloat
readFloat bs =
  Float $ case unpack $ toString bs of
    '+' :: t => go [<] t
    t        => go [<] t
  where
    go : SnocList Char -> List Char -> Double
    go sc []        = cast $ pack (sc <>> [])
    go sc ('_'::cs) = go sc cs
    go sc ('E'::cs) = go (sc:<'e') cs
    go sc (c::cs)   = go (sc:<c) cs

--------------------------------------------------------------------------------
-- Date and Time
--------------------------------------------------------------------------------

%inline
readInt : (Integer -> Maybe a) -> a -> ByteString -> a
readInt f v = fromMaybe v . f . decimal

||| full-date      = date-fullyear "-" date-month "-" date-mday
||| local-date     = full-date
||| date-fullyear  = 4DIGIT
||| date-month     = 2DIGIT  ; 01-12
||| date-mday      = 2DIGIT  ; 01-28, 01-29, 01-30, 01-31 based on month/year
export
fullDate : RExp True
fullDate = repeat 4 digit >> '-' >> month_day
  where
    d29,d30,d31,month_day : RExp True
    d29 = ('0' >> posdigit) <|> (oneof ['1','2'] >> digit)
    d30 = d29 <|> "30"
    d31 = d30 <|> "31"

    month_day =
          (("01"<|>"03"<|>"05"<|>"07"<|>"08"<|>"10"<|>"12") >> '-' >> d31)
      <|> (("04"<|>"06"<|>"09"<|>"11") >> '-' >> d30)
      <|> ("02-" >> d29)

export
readLocalDate : ByteString -> LocalDate
readLocalDate bs =
 let y      := readInt refineYear 0 (take 4 bs)
     m      := readInt intToMonth JAN (take 2 $ drop 5 bs)
  in case refineDay {m} (decimal $ take 2 $ drop 8 bs) of
       Just d  => MkDate y m d
       Nothing => MkDate y JAN 1

-- time-hour      = 2DIGIT  ; 00-23
timeHour : RExp True
timeHour    = (oneof ['0','1'] >> digit) <|> ('2' >> range '0' '3')

-- time-minute      = 2DIGIT  ; 00-59
timeMinute : RExp True
timeMinute  = range '0' '5' >> digit

||| local-time   = partial-time
||| partial-time = time-hour ":" time-minute [ ":" time-second [ time-secfrac ] ]
||| time-secfrac = "." 1*DIGIT
export
localTime : RExp True
localTime = timeHour >> ':' >> timeMinute >> opt (':' >> sec >> opt frac)
  where
    sec,frac : RExp True
    sec  = timeMinute <|> "60"
    frac = '.' >> plus digit

-- TODO: This should go to idris2-bytestring
myPadRight : Nat -> Bits8 -> ByteString -> ByteString
myPadRight n b bs = bs <+> replicate (n `minus` bs.size) b

export
readLocalTime : ByteString -> LocalTime
readLocalTime bs =
  let h := readInt refineHour   0 (take 2 bs)
      m := readInt refineMinute 0 (take 2 $ drop 3 bs)
      s := readInt refineSecond 0 (take 2 $ drop 6 bs)
   in case drop 9 bs of
        BS 0 _ => LT h m s Nothing
        bs     =>
         let bs' := myPadRight 6 byte_0 $ take 6 bs
          in LT h m s $ Just $ readInt refineMicroSecond 0 bs'

||| local-date-time = full-date time-delim partial-time
||| time-delim     = "T" / %x20 ; T, t, or space
export
localDateTime : RExp True
localDateTime = fullDate >> oneof ['T','t',' '] >> localTime

export
readLocalDateTime : ByteString -> LocalDateTime
readLocalDateTime bs =
 let fd := readLocalDate bs
  in LDT fd (readLocalTime $ drop 11 bs)

||| offset-date-time = full-date time-delim full-time
||| full-time = partial-time time-offset
||| time-offset    = "Z" / time-numoffset
||| time-numoffset = ( "+" / "-" ) time-hour ":" time-minute
export
offsetDateTime : RExp True
offsetDateTime =
 let timeNumoffset := oneof ['+','-'] >> timeHour >> ':' >> timeMinute
  in localDateTime >> ('Z' <|> 'z' <|> timeNumoffset)

export
readOffsetDateTime : ByteString -> OffsetDateTime
readOffsetDateTime bs =
 let LDT d t := readLocalDateTime bs
  in ODT d (OT t offset)

  where
    offset : Offset
    offset =
     let bs2@(BS (S _) bv) := takeEnd 6 bs | _ => Z
      in case last bv of
           90  => Z -- 'Z'
           122 => Z -- 'z'
           _   =>
            let h := readInt refineHour 0 (take 2 $ drop 1 bs2)
                m := readInt refineMinute 0 (take 2 $ drop 4 bs2)
                x := if at bv 0 == 43 then Plus else Minus
             in O x h m

-- 557 LOC

-- ;; Key-Value pairs
--
-- keyval = key keyval-sep val
-- key = simple-key / dotted-key
-- val = string / boolean / array / inline-table / date-time / float / integer
--
-- simple-key = quoted-key / unquoted-key
--
-- ;; Quoted and dotted key
--
-- quoted-key = basic-string / literal-string
-- dotted-key = simple-key 1*( dot-sep simple-key )
--
--
-- ;; String
--
-- string = ml-basic-string / basic-string / ml-literal-string / literal-string
--
-- ;; Basic String
--
-- basic-string = quotation-mark *basic-char quotation-mark
--
-- quotation-mark = %x22            ; "
--
-- basic-char = basic-unescaped / escaped
-- escaped = escape escape-seq-char
--
-- escape = %x5C                   ; \
-- escape-seq-char =  %x22         ; "    quotation mark  U+0022
-- escape-seq-char =/ %x5C         ; \    reverse solidus U+005C
-- escape-seq-char =/ %x62         ; b    backspace       U+0008
-- escape-seq-char =/ %x65         ; e    escape          U+001B
-- escape-seq-char =/ %x66         ; f    form feed       U+000C
-- escape-seq-char =/ %x6E         ; n    line feed       U+000A
-- escape-seq-char =/ %x72         ; r    carriage return U+000D
-- escape-seq-char =/ %x74         ; t    tab             U+0009
-- escape-seq-char =/ %x78 2HEXDIG ; xHH                  U+00HH
-- escape-seq-char =/ %x75 4HEXDIG ; uHHHH                U+HHHH
-- escape-seq-char =/ %x55 8HEXDIG ; UHHHHHHHH            U+HHHHHHHH
--
-- ;; Multiline Basic String
--
-- ml-basic-string = ml-basic-string-delim [ newline ] ml-basic-body
--                   ml-basic-string-delim
-- ml-basic-string-delim = 3quotation-mark
-- ml-basic-body = *mlb-content *( mlb-quotes 1*mlb-content ) [ mlb-quotes ]
--
-- mlb-content = basic-char / newline / mlb-escaped-nl
-- mlb-quotes = 1*2quotation-mark
-- mlb-escaped-nl = escape ws newline *( wschar / newline )
--
-- ;; Literal String
--
-- literal-string = apostrophe *literal-char apostrophe
--
-- apostrophe = %x27 ; ' apostrophe
--
-- ;; Multiline Literal String
--
-- ml-literal-string = ml-literal-string-delim [ newline ] ml-literal-body
--                     ml-literal-string-delim
-- ml-literal-string-delim = 3apostrophe
-- ml-literal-body = *mll-content *( mll-quotes 1*mll-content ) [ mll-quotes ]
--
-- mll-content = literal-char / newline
-- mll-quotes = 1*2apostrophe
--
--
-- ;; Array
--
-- array = array-open [ array-values ] ws-comment-newline array-close
--
-- array-open =  %x5B ; [
-- array-close = %x5D ; ]
--
-- array-values =  ws-comment-newline val ws-comment-newline array-sep array-values
-- array-values =/ ws-comment-newline val ws-comment-newline [ array-sep ]
--
-- array-sep = %x2C  ; , Comma
--
-- ;; Table
--
-- table = std-table / array-table
--
-- ;; Standard Table
--
-- std-table = std-table-open key std-table-close
--
--
-- ;; Inline Table
--
-- inline-table = inline-table-open [ inline-table-keyvals ] ws-comment-newline inline-table-close
--
-- inline-table-open  = %x7B  ; {
-- inline-table-close = %x7D  ; }
-- inline-table-sep   = %x2C  ; , Comma
--
-- inline-table-keyvals =  ws-comment-newline keyval ws-comment-newline inline-table-sep inline-table-keyvals
-- inline-table-keyvals =/ ws-comment-newline keyval ws-comment-newline [ inline-table-sep ]

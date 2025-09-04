module Text.TOML.Lexer

import Data.List
import Text.ILex.RExp

%default total

||| wschar =  %x20  ; Space
||| wschar =/ %x09  ; Horizontal tab
export
wschar : RExp True
wschar = ' ' || '\t'

||| ws = *wschar
export
ws : RExp False
ws = star wschar

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

||| basic-unescaped = wschar / %x21 / %x23-5B / %x5D-7E / non-ascii
export
basicUnescaped : RExp True
basicUnescaped =
  wschar || '!' || range32 0x23 0x5b || range32 0x5d 0x7e || nonAscii

||| dot-sep   = ws %x2E ws  ; . Period
export
dotSep : RExp True
dotSep = ws >> '.' >> ws

||| dot-sep   = ws %x2E ws  ; . Period
export
keyvalSep : RExp True
keyvalSep = ws >> '=' >> ws

export
nan : RExp True
nan = opt (oneof ['-','+']) >> "nan"

export
posInf : RExp True
posInf = opt '+' >> "inf"

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
-- keyval-sep = ws %x3D ws ; =
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
-- ;; Integer
--
-- integer = dec-int / hex-int / oct-int / bin-int
--
-- minus = %x2D                       ; -
-- plus = %x2B                        ; +
-- underscore = %x5F                  ; _
-- digit1-9 = %x31-39                 ; 1-9
-- digit0-7 = %x30-37                 ; 0-7
-- digit0-1 = %x30-31                 ; 0-1
--
-- hex-prefix = %x30.78               ; 0x
-- oct-prefix = %x30.6F               ; 0o
-- bin-prefix = %x30.62               ; 0b
--
-- dec-int = [ minus / plus ] unsigned-dec-int
-- unsigned-dec-int = DIGIT / digit1-9 1*( DIGIT / underscore DIGIT )
--
-- hex-int = hex-prefix HEXDIG *( HEXDIG / underscore HEXDIG )
-- oct-int = oct-prefix digit0-7 *( digit0-7 / underscore digit0-7 )
-- bin-int = bin-prefix digit0-1 *( digit0-1 / underscore digit0-1 )
--
-- ;; Float
--
-- float = float-int-part ( exp / frac [ exp ] )
-- float =/ special-float
--
-- float-int-part = dec-int
-- frac = decimal-point zero-prefixable-int
-- decimal-point = %x2E               ; .
-- zero-prefixable-int = DIGIT *( DIGIT / underscore DIGIT )
--
-- exp = "e" float-exp-part
-- float-exp-part = [ minus / plus ] zero-prefixable-int
--
-- ;; Date and Time (as defined in RFC 3339)
--
-- date-time      = offset-date-time / local-date-time / local-date / local-time
--
-- date-fullyear  = 4DIGIT
-- date-month     = 2DIGIT  ; 01-12
-- date-mday      = 2DIGIT  ; 01-28, 01-29, 01-30, 01-31 based on month/year
-- time-delim     = "T" / %x20 ; T, t, or space
-- time-hour      = 2DIGIT  ; 00-23
-- time-minute    = 2DIGIT  ; 00-59
-- time-second    = 2DIGIT  ; 00-58, 00-59, 00-60 based on leap second rules
-- time-secfrac   = "." 1*DIGIT
-- time-numoffset = ( "+" / "-" ) time-hour ":" time-minute
-- time-offset    = "Z" / time-numoffset
--
-- partial-time   = time-hour ":" time-minute [ ":" time-second [ time-secfrac ] ]
-- full-date      = date-fullyear "-" date-month "-" date-mday
-- full-time      = partial-time time-offset
--
-- ;; Offset Date-Time
--
-- offset-date-time = full-date time-delim full-time
--
-- ;; Local Date-Time
--
-- local-date-time = full-date time-delim partial-time
--
-- ;; Local Date
--
-- local-date = full-date
--
-- ;; Local Time
--
-- local-time = partial-time
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
-- ws-comment-newline = *( wschar / [ comment ] newline )
--
-- ;; Table
--
-- table = std-table / array-table
--
-- ;; Standard Table
--
-- std-table = std-table-open key std-table-close
--
-- std-table-open  = %x5B ws     ; [ Left square bracket
-- std-table-close = ws %x5D     ; ] Right square bracket
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
--
-- ;; Array Table
--
-- array-table = array-table-open key array-table-close
--
-- array-table-open  = %x5B.5B ws  ; [[ Double left square bracket
-- array-table-close = ws %x5D.5D  ; ]] Double right square bracket
--
-- ;; Built-in ABNF terms, reproduced here for clarity
--
-- ALPHA = %x41-5A / %x61-7A ; A-Z / a-z
-- DIGIT = %x30-39 ; 0-9
-- HEXDIG = DIGIT / "A" / "B" / "C" / "D" / "E" / "F"

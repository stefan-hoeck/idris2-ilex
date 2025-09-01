# ilex: Generating fast Lexers from an Idris2 DSL

This is a library for generating performant lexers that can
be derived from a simple regular expression DSL (domain specific language).
However, this library also offers a way to enhance the lexers to become proper
parsers. The following list describes the main characteristics
of this library:

* Performance: Lexers are compiled at runtime to discrete, array-backed
  state machines that operate directly on raw byte arrays and therefore
  perform exceedingly well in comparison with common combinator-based
  solutions that operate on lists of characters.
* Stack safety: The drivers running the lexers over byte arrays are
  tail recursive and therefore safe to use on backends with limited
  stack size such as the JavaScript backends.
* Convenience: A high-level DSL for describing the regular expressions
  used in the lexers is provided together with a few basic conversion
  functions to extract lexicographic tokens from the matched byte
  arrays.
* Full unicode (UTF-8) support: Regular expressions based on
  characters (unicode code points) are automatically converted to
  state machines that handle non-ascii code points correctly at
  the byte level.
* Streaming: It is straight forward to use the state machines in
  a setting where large amounts of data have to be streamed chunk-wise
  without loading them all at once into memory.
* Context Awareness: It is possible to combine several lexers into
  a single context-aware tokenizer. Common use cases for this are,
  for instance, the lexing of string literals with support for
  character escape sequences, string interpolation where
  string literals can contain regular code snippets,
  or nested multi-line comments.
* Parsing: As an experimental feature, we explore the possibilities
  this library offers for writing proper LR-parsers by keeping
  track of the parsing state in a (possibly indexed) stack-like
  data type. While this approach gives us all of the benefits
  listed above, it remains yet to be seen if writing parsers
  in such a way is convenient enough to compete with the well
  established approaches offered by parser generators, parser combinators,
  or hand-written recursive descent parsers.

This is a literate Idris file, so we start with some imports and
a utility function used to run the lexers and parsers described
in this section and print their results.

```idris
module README

import Derive.Prelude
import Examples.Basics
import Examples.Types
import FS.Posix
import FS.System
import IO.Async.Loop.Epoll
import IO.Async.Loop.Posix
import Text.ILex.FS

%default total
%language ElabReflection
%hide Data.Linear.(.)

pretty : Interpolation e => Show a => Either e (List a) -> IO ()
pretty (Left x)   = putStrLn $ interpolate x
pretty (Right vs) = traverse_ printLn vs
```

## A basic CSV Lexer

A [lexer](https://en.wikipedia.org/wiki/Lexical_analysis) cuts text
(or a raw byte vector) into syntactically meaningful tokens. For
instance, assume we have a CSV file with the following content:

```idris
csvStr1 : String
csvStr1 =
  """
  foo,12,true
  bar,13,true
  baz,14,false
  """
```

What kind of token can we recognize here? We certainly have the
commas separating the fields on every line. We also have line
breaks separating table rows. Between those, we have arbitrary
data. Let us start with these very basic observations and
define and test a lexer for this structure. Since we are
going to implement several iterations of a CSV lexer,
we use an integer suffix in our names:

```idris
data CSV0 : Type where
  Comma0 : CSV0
  NL0    : CSV0
  Cell0  : String -> CSV0

%runElab derive "CSV0" [Show,Eq]

Interpolation CSV0 where interpolate = show
```

The data constructors of `CSV0` describe the different
tokens we can recognize in a (very basic) CSV
file. Without further ado, here is our first CSV lexer:

```idris
csv0 : L1 q Void CSV0
csv0 =
  lexer
    [ ctok0 ',' Comma0
    , nltok0 '\n' NL0
    , readTok0 (plus (dot && not ',')) Cell0
    ]
```

Before we describe the definition above in some detail, let's quickly
test it at the REPL:

```repl
README> :exec pretty (parseString csv0 Virtual csvStr1)
B {val = Cell0 "foo", bounds = ...}
...
```

As you can see, the input has been cut into a list of tokens, each
annotated with the region (its *bounds*) where in the byte array
it appeared. Please note
that the functions in this library cannot be evaluated directly at the
REPL, so we have to actually compile a small program and run it using
`:exec`.

Feel free to experiment with this a bit. For instance, you might want to
force an error by passing it a string that contains a tab character (`"\t"`),
something our lexer cannot yet handle. You will note that you'll get a
detailed error message highlighting the exact position of the error
in the input string.

Now, let us have a closer look at the definition of `csv0`: We use
a `TokenMap` to describe a lexer: a list of regular expressions each paired
with a conversion function. Character literals just match themselves,
so the first entry matches a single comma and converts it to a `Comma0`
value. The same goes for the line break character.

Cell tokens are a bit more involved: We expect one or more (`plus`)
printable characters (`dot`) that are also not commas (`&& not ','`)
and convert them to a `Cell0` token.

A quick note about the types: `Lexer b Void CSV0` describes a
lexer that uses `b` for its token bounds (there are different
types of bounds we support; in many cases, we want to keep this
abstract), `Void` is the type of custom errors our lexer throws
(no custom errors in this case, because `Void` is uninhabited),
and `CSV0` is the token type the lexer generates. We will later
see that this is actually a utility alias for something more
versatile.

### Additional Cell Types

While our first example already demonstrates how we can tokenize
a very basic language, one could argue that something similar could be
achieved just by using functions `lines` and `split` from `Data.String`.
Therefore, we are going to enhance our lexer in several ways.

First, we'd like to support boolean literals (`"true"` and `"false"`).
Next, we'd like to support positive and negative integer literals.
And finally, we'd like to be able to not only read data with
Unix-style line breaks, but also ASCII sequences from other
systems.

First, our updated token type:

```idris
data CSV1 : Type where
  Comma1 : CSV1
  NL1    : CSV1
  Txt1   : String -> CSV1
  Bool1  : Bool -> CSV1
  Int1   : Integer -> CSV1

%runElab derive "CSV1" [Show,Eq]

Interpolation CSV1 where interpolate = show
```

And here's the corresponding lexer:

```idris
linebreak : RExp True
linebreak = '\n' <|> "\n\r" <|> "\r\n" <|> '\r' <|> '\RS'

csv1 : L1 q Void CSV1
csv1 =
  lexer
    [ ctok0 ',' Comma1
    , nltok0 linebreak NL1
    , stok0 "true" (Bool1 True)
    , stok0 "false" (Bool1 False)
    , convTok0 (opt '-' >> decimal) (Int1 . integer)
    , readTok0 (plus (dot && not ',')) Txt1
    ]
```

The above is *much* more powerful than our original `csv0` lexer, and
trying to implement this manually might be quite a frustrating
experience. Go ahead and experiment with this a bit at the REPL, and
see, if it behaves as expected.

### Overlapping Expressions and Maximal Munch

Before we continue enhancing our lexer, we have to quickly explain
two important concepts. When you look at the definition of `csv1`,
you will note that there is some overlap between certain token types.
For instance, `"true"` could be interpreted both as a boolean
and as a text token. In addition `"\r\n"` could be read as
one or two line breaks. Go ahead and check at the REPL
how `parseString` deals with these cases.

As you can easily verify, `"foo"` is interpreted as a single text token
instead of three tokens (one for each character), even though an interpretation
as three tokens would be in agreement with the regular expressions
we defined. Likewise, '"\r\n"' is interpreted as a single
line break instead of two. This strategy is called
the [maximal munch](https://en.wikipedia.org/wiki/Maximal_munch)
or *longest match* principle: The lexer tries to generate the longest possible
token that matches an expression.

In addition, there can be some overlap between tokens of the same
length, so that they could be interpreted in more than one way.
In this case, the first matching expression takes precedence.
Therefore, `"true"` is interpreted as a boolean and `"123"` as
an integer, although both would also be valid text tokens.

### Dealing with Whitespace

We'd like to further generalize our lexer, so that it properly deals
with whitespace that might surround our tokens. We expect the
following to be interpreted the same way as `csvStr1`:

```idris
csvStr2 : String
csvStr2 =
  """
    foo ,  12,  true\t\t
  bar,13  ,   true
    baz,  14,false
  """
```

There are several strategies that could help us here. For instance,
we could enhance all our tokens to accept a pre- and postfix of
arbitrary whitespace. However, this would require us to manually
trim text tokens, and it would lead to quite some code duplication
in our token expressions. The alternative is to add a specific whitespace
token. With this, only the text token has to be adjusted: It must
now start and end with a non-whitespace character.

```idris
text : RExp True
text = nonspace >> opt (star textChar >> nonspace)
  where
    nonspace, textChar : RExp True
    textChar = dot && not ','
    nonspace = textChar && not ' ' && not '"'
```

The above defines a text character as any printable character (`dot`)
that's not a comma (`&& not ','`), and a non-space character as
a text character that's not a space (`&& not ' '`) (and not a
quote, which we are going to need once we look at quoted strings). A text
token is then a non-space character followed by an optional
suffix consisting of an arbitrary number of text characters
terminated by another non-space.

With this, we can now define a whitespace token that we silently
drop during lexing:

```idris
spaceExpr : RExp True
spaceExpr = plus $ oneof [' ', '\t']

csv1_2 : L1 q Void CSV1
csv1_2 =
  lexer
    [ ctok0 ',' Comma1
    , nltok0 linebreak NL1
    , stok0 "true" (Bool1 True)
    , stok0 "false" (Bool1 False)
    , convTok0 (opt '-' >> decimal) (Int1 . integer)
    , readTok0 text Txt1
    , (spaceExpr, spaces 0)
    ]
```

### Quoted Text

Currently, our CSV lexer cannot process any text that contains
commas. Likewise, it is not possible to include any control
characters such as tabs or line breaks in our text tokens.
We'd now like to add support for these.

Again, there are several strategies we could use here. What we are
going to do is to add support for quoted strings. This will allow
us to have text with commas by wrapping the corresponding text
in double quotes. Likewise, it allows us to have
text tokens that start or end with whitespace. However, a quoted
string can no longer contain double quote characters, so we need
a way to escape those. Likewise, we need a way to escape the control
characters we'd like to support.

Here's a regular expression for quoted strings:

```idris
quoted : RExp True
quoted = '"' >> star qchar >> '"'
  where
    qchar : RExp True
    qchar =
          (dot && not '"' && not '\\')
      <|> #"\""#
      <|> #"\n"#
      <|> #"\r"#
      <|> #"\t"#
      <|> #"\\"#
```

With this, we can enhance our lexer:

```idris
unquote : ByteString -> String

csv1_3 : L1 q Void CSV1
csv1_3 =
  lexer
    [ ctok0 ',' Comma1
    , nltok0 linebreak NL1
    , stok0 "true" (Bool1 True)
    , stok0 "false" (Bool1 False)
    , convTok0 (opt '-' >> decimal) (Int1 . integer)
    , readTok0 text Txt1
    , convTok0 quoted (Txt1 . unquote)
    , (spaceExpr, spaces 0)
    ]
```

In order to keep things simple, we are going use character lists
to implement `unquote`:

```idris
unquote = go [<] . unpack . toString
  where
    go : SnocList Char -> List Char -> String
    go sc []              = pack (sc <>> [])
    go sc ('\\'::'"' ::xs) = go (sc :< '"') xs
    go sc ('\\'::'\\'::xs) = go (sc :< '\\') xs
    go sc ('\\'::'t' ::xs) = go (sc :< '\t') xs
    go sc ('\\'::'n' ::xs) = go (sc :< '\n') xs
    go sc ('\\'::'r' ::xs) = go (sc :< '\r') xs
    go sc ('"'::xs)        = go sc xs
    go sc (x::xs)          = go (sc :< x) xs
```

We are going to look at how to do this in a more performant
and elegant manner in a moment.

I suggest you fire up a REPL session and experiment a bit with what kind
of tokens our lexer is now capable of recognizing.

As promised, here's an alternative version of `unquote`: We just tokenize
the byte string again. This avoids having to convert the byte string
to a list of characters and traversing that. In general, this should be
faster than the above, but I suggest to profile this properly if it
is used in performance critical code.

```idris
lexUQ : L1 q Void String
lexUQ =
  lexer
    [ stok0 #"\""# "\""
    , stok0 #"\\"# "\\"
    , stok0 #"\n"# "\n"
    , stok0 #"\r"# "\r"
    , stok0 #"\t"# "\t"
    , stok0 #"""#  ""
    , readTok0 (plus (dot && not '"' && not '\\')) id
    ]

fastUnquote : ByteString -> String
fastUnquote bs =
  case parseBytes lexUQ Virtual bs of
    Left  _  => ""
    Right xs => fastConcat (map val xs)
```

## Parsing CSV Files

We are now going to learn how to properly parse
comma separated values. Instead of just listing the
lexicographic tokens, we are going to actually accumulate
these tokens into a larger data structure. We therefore
start with a definition of said data structure:

```idris
data Cell : Type where
  Null  : Cell
  CStr  : String -> Cell
  CBool : Bool -> Cell
  CInt  : Integer -> Cell

%runElab derive "Cell" [Show,Eq]

record Line where
  constructor L
  nr    : Nat
  cells : List Cell

%runElab derive "Line" [Show,Eq]

0 Table : Type
Table = List Line
```

We go back to using a more basic lexer for the time being
(no quoted strings with escape sequences; we'll look at
those further below), but our token type will already
include everything needed to parser quoted strings with
escape sequences:

```idris
data CSV : Type where
  Comma : CSV
  NL    : CSV
  Quote : CSV
  Str   : String -> CSV
  Cll   : Cell -> CSV

%runElab derive "CSV" [Show,Eq]

Interpolation CSV where interpolate = show
```

The new thing is, that instead of a `Lexer`, we just
define a discrete finite automaton (DFA) for dealing
with the tokenization part. We'll see why in a moment:

```idris
-- csvDFA : DFA (Tok e CSV)
-- csvDFA =
--   dfa
--     [ (','               , const Comma)
--     , ('"'               , const Quote)
--     , (linebreak         , const NL)
--     , ("true"            , const (Cll $ CBool True))
--     , ("false"           , const (Cll $ CBool False))
--     , (opt '-' >> decimal, bytes (Cll . CInt . integer))
--     , (text              , txt (Cll . CStr))
--     , (spaces            , Ignore)
--     ]
```

As you can see, the automaton emits tokens for commas, line breaks,
and complete data fields (cells). The quote character gets special
treatment and will lead to a `Quote` token being emitted. More on
this when we talk about string literals.

### State and Parsing

With  the DFA defined above we can already define a proper
CSV parser by implementing a bunch of state transitions based
on the tokens we encounter. We build lines from top to bottom
keeping track of the current line number. Likewise, we
build each line from left to right. Finally, we have to
keep track of where in the parsing process we are (at the
beginning of a line, after a comma, or after a value). We
use a simple tag to keep track of this.

```idris
data Tag = New | Val | Com

data CState : Type -> Type where
  CL : Nat -> SnocList Line -> SnocList Cell -> Tag -> CState b
  CS : Nat -> SnocList Line -> SnocList Cell -> b -> SnocList String -> CState b
```

As you can see, our parser state consists of two data constructors
and is parameterized by the type of bounds provided by the
driver we use for parsing. The `CL` data constructor corresponds
to a partially parsed line (line number, lines parsed so far,
cells parsed so far, tag describing the current position) as
described above. Constructor `CS` holds the same information,
but we use it to accumulate a string literal. We will look
at this one more closely in the next section.

The main complexity comes from defining the state transitions.
Given a value of type `Input b s t` (holding the current token,
the current parser state, and the token bounds), we produce an
updated parser state or an error.

Here's the corresponding state transition function:

```idris
-- new : Nat -> SnocList Line -> Either e (CState b)
-- new n sl = Right $ CL (S n) sl [<] New
--
-- cv : Nat -> SnocList Line -> SnocList Cell -> Either e (CState b)
-- cv n sl sc = Right $ CL n sl sc Val
--
-- cc : Nat -> SnocList Line -> SnocList Cell -> Either e (CState b)
-- cc n sl sc = Right $ CL n sl sc Com
--
-- step2 : Input b (CState b) CSV -> ParseRes b e (CState b) CSV
-- step2 (I t (CS _ _ _ bs _) b) = unclosed bs Quote
-- step2 (I t (CL n sl sc tg) b) =
--   case t of
--     Comma => case tg of
--       Val => cc n sl sc
--       _   => cc n sl (sc :< Null)
--     NL    => case tg of
--       New => new n sl
--       Val => new n (sl :< L n (sc <>> []))
--       Com => new n (sl :< L n (sc <>> [Null]))
--     Cll x => case tg of
--       Val => unexpected b t
--       _   => cv n sl (sc :< x)
--     Quote => case tg of
--       Val => unexpected b t
--       _   => Right $ CS n sl sc b [<]
--     _     => unexpected b t
```

In the first line, we just fail with an error in case we are
currently in a string literal. This will be fixed in the next
section. Note, however, that the error we produce here tells us
that an opening quote has not properly been closed. In order to
get a nice visualization of this, we use the bounds of the opening
quote to describe where in the input string the error happened.

The rest is plain pattern matches on the lexicographic token:

* After a comma, we change the state's tag. In case the last token
  was not a value, we append an empty cell (`Null`).
* After a line break, we start a new line and append the current
  line to the list of lines. Like with a comma, we might append
  an empty cell. Note, that we do not generate entries for empty
  lines. This is an opinionated choice. You might decide to do
  otherwise (or let client code decide via a settings parameter)
  in your own CSV parser
* After a value, we append the value to the list of cells unless
  the last token was already a value, in which case we fail with
  an error.
* After a quote, we start a partial string or fail with an error
  (in case the last token was a value).

Hard part's over. To complete our parser, we need two additional
functions. The first is related to streaming large chunks of
data. We will come back to this in a later section. For now,
suffice to say that in a data stream, we'd like to occasionally
emit all the lines we have encountered so far and remove them
from the accumulated state in order not to blow up our application's
memory consumption. Here's the utility to do this:

```idris
chunkCSV : CState b -> (CState b, Maybe Table)
chunkCSV (CL k sx sy x)      = (CL k [<] sy x, maybeList sx)
chunkCSV (CS k sx sy x sstr) = (CS k [<] sy x sstr, maybeList sx)
```

Finally, we need to finish things once we reach the end of
input. Again, we might fail with an exception in case
we are in the middle of something unfinished. To keep
things simple, we just invoke `step2` with a line break
token:

```idris
lines : CState b -> List Line
lines (CL _ sx _ _)   = sx <>> []
lines (CS _ sx _ _ _) = sx <>> []

-- eoiCSV : b -> CState b -> ParseRes b e Table CSV
-- eoiCSV bs s = lines <$> step2 (I NL s bs)
```

With these utilities defined, we can assemble everything
in a proper parser:

```idris
init : CState b
init = CL 1 [<] [<] New

-- csv2 : Parser b Void CSV Table
-- csv2 = P init (const csvDFA) step2 chunkCSV eoiCSV
```

As you can see, the parser consists of the initial state,
one or several DFAs and three state conversion functions.

You might wonder about the `const csvDFA` part: As we will see
in the next section, the automaton we use for creating the next
token can change depending on the current parser state. This allows
us to make our tokenizer context sensitive. In this more basic parser,
we use only one automaton.

### Quoted Strings and Escape Sequences

We are now going to look at how to handle quoted string
literals with escape sequences. First, we note that an
escape sequence is always started with a backquote (`\`),
so the occurrences of these break the whole string token
into smaller parts. That's why we use a `SnocList` in our
parser state for representing a partially parsed string
literal. Since the tokens we expect within a quoted string
literal are completely different from the ones encountered outside
of quoted strings, it makes sense to handle these in a
separate automaton:

```idris
-- strDFA : DFA (Tok e CSV)
-- strDFA =
--   dfa
--     [ ('"',    const Quote)
--     , (#"\""#, const $ Str "\"")
--     , (#"\\"#, const $ Str "\\")
--     , (#"\n"#, const $ Str "\n")
--     , (#"\r"#, const $ Str "\r")
--     , (#"\t"#, const $ Str "\t")
--     , (linebreak, const NL)
--     , (plus (dot && not '"' && not '\\'), txt Str)
--     ]
```

You might wonder, why we include the line break token in
this DFA. As you will see in a moment, this will allow us to
generate more precise error messages in case of quoted string
literals without a closing quote.

We can make use of the more basic parser from the last section
to implement the state transition function. The only new thing
is that we can now append parts of a string literal to
the corresponding token state as well as close that state
once we arrive at the closing quote:

```idris
-- stepCSV : Input b (CState b) CSV -> ParseRes b e (CState b) CSV
-- stepCSV i@(I t (CS n sl sc bs ss) b) =
--   case t of
--     Quote => cv n sl (sc :< CStr (snocPack ss))
--     Str x => Right $ CS n sl sc bs (ss :< x)
--     _     => step2 i
-- stepCSV i = step2 i
```

The functions for processing chunks and end of input need not
be adjusted. However, we now want to use a proper context
sensitive lexer. The DFA to use will therefore depend on the
current parser state. While we are in the middle of a quoted
string literal, we want to use `strDFA`, otherwise we'll use
the default (`csvDFA`):

```idris
-- lexCSV : CState b -> DFA (Tok e CSV)
-- lexCSV (CL {}) = csvDFA
-- lexCSV (CS {}) = strDFA

-- csv : Parser b Void CSV Table
-- csv = P (CL 1 [<] [<] New) lexCSV stepCSV chunkCSV eoiCSV
```

With all things properly tied up, we can now test our
full-fledged CSV parser, for instance, with the following
example input:

```idris
csvStr3 : String
csvStr3 =
  #"""
   entry 1, "this is a \"test\""         , true  ,  12
   entry 2, "below is an empty line"     , false ,   0

   entry 3, "this one has an empty cell" ,       , -20
   entry 4, "finally, a backslash: \\"   ,true   ,   4
  """#
```

### Error Handling

From a user's point of view, one of the most important aspects
when writing a parser is to come up with helpful error messages.
I strongly advise you to have a closer look at the data
types and their constructors in `Text.ILex.Error`. In general,
an `InnerError` is paired with a file context (filename plus exact
position or range where the error occurred) and then pretty printed
whenever something goes wrong.

`InnerError` is parameterized over the token type as well as a
custom error type for those situations where the existing
error constructors are not descriptive enough.
In our examples, this is set to the uninhabited
type `Void`, meaning that in our case, there will be no
custom errors.

Below are a couple of erroneous CSV strings. Feel free to
run our parser against those and check out the error messages
we get:

```idris
twoValues : String
twoValues = "this is wrong, \"foo\" false"

invalidTab : String
invalidTab = "this is wrong, foo, false, \"Ups: \t\", bar"

unclosedQuote : String
unclosedQuote = "this is wrong, foo, false, \"Ups , bar"
```

The error message from the last example is important: Instead
of complaining about having reached the end of input (which, in
my opinion, would be rather unspecific), we mark the opening
quote that has not properly been closed.

We'd like to do the same in case we arrive at a line break
in the middle of a quoted string. Again, the resulting error
message will be more specific. This is only possible by
including the line break token `NL` as one of the tokens
emitted by the string DFA. Here's an example where this is
relevant. Feel free to remove the `linebreak` line from
the definition of `strDFA` and re-check the parser's behavior
at the REPL.

```idris
unclosedMultiline : String
unclosedMultiline =
  """
    foo, "this is a, 12
    bar, test, 13
  """
```

## Streaming Files

Functions such as `parse` and `parseString` are supposed to process a
(byte)string as a whole, so the whole data needs to fit into memory.
Sometimes, however, we would like to process huge amounts of data.
Package *ilex-streams*, which is also part of this project, provides
utilities for this occasion. Fortunately, data type `Parser` already
holds all the ingredients to process large data sets in chunks and
emit the values accumulated so far once after each chunk of data.

We are going to demonstrate how this is done when reading a large
file containing CSV-encoded data. First, we define a type alias
and runner for the data stream
(see the [idris2-streams library](https://github.com/stefan-hoeck/idris2-streams)
for proper documentation about `Pull` and `Stream`). Since
we want to read stuff from file descriptors we use
the `Async` monad (from [idris2-async](https://github.com/stefan-hoeck/idris2-async))
with polling capabilities. We also want to deal with possible errors -
parsing errors as well as errors from the operating system. This
leads to the following type alias for our data stream plus a
runner that will pretty print all errors to `stderr`:

```idris
-- 0 Prog : Type -> Type -> Type
-- Prog o r = AsyncPull Poll o [StreamError CSV Void, Errno] r
--
-- covering
-- runProg : Prog Void () -> IO ()
-- runProg prog =
--  let handled := handle [stderrLn . interpolate, stderrLn . interpolate] prog
--   in epollApp $ mpull handled
```

If the above is foreign to you, please work through the tutorials
provided with the *async* and *streams* libraries.

And here's an example how to stream a single, possibly huge, CSV file
(this will print the total number of non-empty CSV-lines encountered):

```idris
-- streamCSV : String -> Prog Void ()
-- streamCSV pth =
--   lift1 (buf 0xffff) >>= \buf =>
--        readRawBytes buf pth
--     |> P.mapOutput (FileSrc pth,)
--     |> streamParse csv
--     |> C.count
--     |> printLnTo Stdout
```

Functions `readBytes`, `mapOutput`, and `printLnTo` are just standard
streaming utilities, while function `streamParse` is provided by
the *ilex-streams* library. With the above, you can stream arbitrarily
large CSV files in constant memory.

However, there are some minor differences compared to tokenizing whole
strings of data:

* While we still follow a maximum-munch lexing strategy, there will
  be no backtracking to previously encountered terminal states. This is
  fine for most data formats, so it shouldn't be a big deal in practice.
* For obvious reasons, we don't store the whole byte stream in memory,
  so error messages will only contain the region (start and end line and
  column) where the error occurred but not a highlighted excerpt of the
  string with the error.

```idris
-- streamCSVFiles : Prog String () -> Buf -> Prog Void ()
-- streamCSVFiles pths buf =
--      flatMap pths (\p => readRawBytes buf p |> P.mapOutput (FileSrc p,))
--   |> streamParse csv
--   |> C.count
--   |> printLnTo Stdout
```

Below is a `main` function so you can test our CSV parser against
your own CSV files (or some files downloaded from the web). I strongly
suggest you experiment some more with this.
For instance, you might add support
for single-line comments: Everything after a specific character
(for instance `'#'`) until the end of line is to be considered
a comment and should be dropped.

You could also add support for floating-point literals,
single characters (in single quotes like in Idris), date and time
values and so on.

```idris
-- covering
-- main : IO ()
-- main = runProg $ lift1 (buf 0xffff) >>= streamCSVFiles (P.tail args)
```

In order to compile this and check it against your own
CSV files:

```sh
pack -o csv exec examples/src/README.md
examples/build/exec/csv ~/downloads/*.csv
```

<!-- vi: filetype=idris2:syntax=markdown
-->

# ilex: Generating fast Lexers from an Idris2 DSL

This is a library for generating performant lexers that can
be derived from a simple regular expression DSL.

This is a literate Idris file, so we start with some imports.

```idris
module README

import Derive.Prelude
import Examples.Basics
import Examples.Types
import FS.Posix
import IO.Async.Loop.Epoll
import IO.Async.Loop.Posix
import Text.ILex.FS

%default total
%language ElabReflection
%hide Data.Linear.(.)
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
breaks separating table rows. In between those, we have arbitrary
data. Let us start with these very basic observations and
define and test a lexer for this structure. Since we are
going to implement several iterations of a `.csv` lexer,
we use an integer suffix in our names:

```idris
data CSV0 : Type where
  Comma0 : CSV0
  NL0    : CSV0
  Cell0  : String -> CSV0

%runElab derive "CSV0" [Show,Eq]
```

Without further ado, here is our first `.csv` lexer:

```idris
csv0 : Lexer Void CSV0
csv0 =
  lexer
    [ (','                  , Const Comma0)
    , ('\n'                 , Const NL0)
    , (plus (dot && not ','), txt (Cell0 . toString))
    ]
```

Before we describe the definition above in some detail, let's quickly
test it at the REPL:

```repl
README> :exec printLn (lexString Virtual csv0 csvStr1)
Right [ ... ]
```

As you can see, the input has been cut into a list of tokens. Please note
that the functions in this library cannot be evaluated directly at the
REPL, so we have to actually compile a small program and run it using
`:exec`.

Now, let us have a closer look at the definition of `csv0`: We use
a `TokenMap` to describe a lexer: a list of regular expressions each paired
with a conversion function. Character literals just match themselves,
so the first entry matches a single comma and converts it to a `Comma0`
value. The same goes for the line break character.

Cell tokens are a bit more involved: We expect one or more (`plus`)
printable characters (`dot`) that are also not commas (`&& not ','`)
and convert them to a `Cell0` token. Please note that `txt` converts
a `ByteString`, so we use `toString` to convert it correctly.

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
  EOI    : CSV1

%runElab derive "CSV1" [Show,Eq]
```

And here's the corresponding lexer:

```idris
linebreak : RExp True
linebreak = '\n' <|> "\n\r" <|> "\r\n" <|> '\r' <|> '\RS'

csv1 : Lexer Void CSV1
csv1 =
  setEOI EOI $ lexer
    [ (','                  , Const Comma1)
    , (linebreak            , Const NL1)
    , ("true"               , Const (Bool1 True))
    , ("false"              , Const (Bool1 False))
    , (decimal              , txt (Int1 . decimal))
    , ('-' >> decimal       , txt (Int1 . negate . decimal . drop 1))
    , (plus (dot && not ','), txt (Txt1 . toString))
    ]
```

The above is *much* more powerful that our original `csv0` lexer, and
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
how `lexString` deals with these cases.

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
spaces : RExp True
spaces = plus $ oneof [' ', '\t']

csv1_2 : Lexer Void CSV1
csv1_2 =
  setEOI EOI $ lexer
    [ (','           , Const Comma1)
    , (linebreak     , Const NL1)
    , ("true"        , Const (Bool1 True))
    , ("false"       , Const (Bool1 False))
    , (decimal       , txt (Int1 . decimal))
    , ('-' >> decimal, txt (Int1 . negate . decimal . drop 1))
    , (text          , txt (Txt1 . toString))
    , (spaces        , Ignore)
    ]
```

### Quoted Text

Currently, our `.csv` lexer cannot process any text that contains
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

csv1_3 : Lexer Void CSV1
csv1_3 =
  setEOI EOI $ lexer
    [ (','           , Const Comma1)
    , (linebreak     , Const NL1)
    , ("true"        , Const (Bool1 True))
    , ("false"       , Const (Bool1 False))
    , (decimal       , txt (Int1 . decimal))
    , ('-' >> decimal, txt (Int1 . negate . decimal . drop 1))
    , (text          , txt (Txt1 . toString))
    , (quoted        , txt (Txt1 . unquote))
    , (spaces        , Ignore)
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

I suggest you fire up a REPL session an experiment a bit with what kind
of tokens our lexer is now capable of recognizing.

As promised, here's an alternative version of `unquote`: We just tokenize
the byte string again. This avoids having to convert the byte string
to a list of characters and traversing that. In general, this should be
faster than the above, but I suggest to profile this properly if it
is used in performance critical code.

```idris
lexUQ : Lexer Void String
lexUQ =
  lexer
    [ (#"\""#, Const "\"")
    , (#"\\"#, Const "\\")
    , (#"\n"#, Const "\n")
    , (#"\r"#, Const "\r")
    , (#"\t"#, Const "\t")
    , (#"""# , Ignore)
    , (plus (dot && not '"' && not '\\'), txt toString)
    ]

fastUnquote : ByteString -> String
fastUnquote bs =
  case lexBytes Virtual lexUQ bs of
    Left  _  => ""
    Right xs => fastConcat (map val xs)
```

## Streaming Files

Functions such as `lex` and `lexBytes` are supposed to tokenize a
(byte)string as a whole, so the whole data needs to fit into memory.
Sometimes, however, we would like to process huge amounts of data.
Package *ilex-streams*, which is also part of this project, provides
utilities for this occasion.

We are going to demonstrate how this is done when reading a large
file containing JSON-encoded data. First, we define a type alias
and runner for the data stream
(see the [idris2-streams library](https://github.com/stefan-hoeck/idris2-streams)
for proper documentation about `Pull` and `Stream`). Since
we want to read stuff from file descriptors, so we use
the `Async` monad (from [idris2-async](https://github.com/stefan-hoeck/idris2-async))
with polling capabilities. We also want to deal with possible errors -
parsing errors as well as errors from the operating system. This
leads to the following type alias for our data stream plus a
runner that will pretty print all errors to `stderr`:

```idris
0 Prog : Type -> Type -> Type
Prog o r = AsyncPull Poll o [StreamError JSON Void, Errno] r

covering
runProg : Prog Void () -> IO ()
runProg prog =
 let handled := handle [stderrLn . interpolate, stderrLn . interpolate] prog
  in epollApp $ mpull handled
```

And here's an example how to stream a single, possibly huge, JSON file
(this will print the number of tokens found in each chunk of data read):

```idris
streamJSON : String -> Prog Void ()
streamJSON pth =
     readBytes pth
  |> P.mapOutput (FileSrc pth,)
  |> streamLex json
  |> P.mapOutput length
  |> printLnTo Stdout
```

Functions `readBytes`, `mapOutput`, and `printLnTo` are just standard
streaming utilities, while function `streamLex` is provided by
the *ilex-streams* library. With the above, you can stream arbitrarily
large JSON files in constant memory.

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
covering
main : IO ()
main = runProg $ streamJSON "/home/gundi/downloads/large-file.json"
```

<!-- vi: filetype=idris2:syntax=markdown
-->

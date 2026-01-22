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
import Syntax.T1
import Text.ILex.FS

%default total
%language ElabReflection
%hide Data.Linear.(.)
%hide Language.Reflection.TT.Str

pretty :
     {auto ie : Interpolation e}
  -> {auto ia : Interpolation a}
  -> Parser1 (BoundedErr e) r s (List a)
  -> String
  -> IO ()
pretty p s =
  case parseString p Virtual s of
    Left x   => putStrLn $ interpolate x
    Right vs => traverse_ (putStrLn . interpolate) vs
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
csv0 : L1 q Void 1 CSV0
csv0 =
  lexer
    [ ctok ',' Comma0
    , nltok '\n' NL0
    , readTok (plus (dot && not ',')) Cell0
    ]
```

Before we describe the definition above in some detail, let's quickly
test it at the REPL:

```repl
README> :exec pretty csv0 csvStr1
Cell0 "foo": 1:1--1:4
Comma0: 1:4--1:5
Cell0 "12": 1:5--1:7
Comma0: 1:7--1:8
Cell0 "true": 1:8--1:12
NL0: 1:12--1:13
Cell0 "bar": 2:1--2:4
Comma0: 2:4--2:5
Cell0 "13": 2:5--2:7
Comma0: 2:7--2:8
Cell0 "true": 2:8--2:12
NL0: 2:12--2:13
Cell0 "baz": 3:1--3:4
Comma0: 3:4--3:5
Cell0 "14": 3:5--3:7
Comma0: 3:7--3:8
Cell0 "false": 3:8--3:13
```

As you can see, the input has been cut into a list of tokens, each
annotated with the region (its *bounds*) where in the string it appeared.
Please note that the functions in this library cannot be evaluated directly
at the REPL, so we have to actually compile a small program and run it using
`:exec`.

Feel free to experiment with this a bit. For instance, you might want to
force an error by passing it a string that contains a tab character (`"\t"`),
something our lexer cannot yet handle. You will note that you'll get a
detailed error message highlighting the exact position of the error
in the input string.

Now, let us have a closer look at the definition of `csv0`: We use
a `TokenMap` to describe a lexer: a list of regular expressions each paired
with a conversion function. To create these pairs, we often use
one of the utility functions from `Text.ILex.Stack`.
Functions `ctok`, for instance, matches a fixed number
of characters and emits a properly bounded token.

Cell tokens are a bit more involved: We expect one or more (`plus`)
printable characters (`dot`) that are also not commas (`&& not ','`)
and convert them to a `Cell0` token. For such variable length tokens,
we can use utilities `readTok` (if we want to the token as a `String`)
or `convTok` (if we want the token as a `ByteString`).

Please note, that the utilities described so far assume that there
are no line breaks in the tokens they recognize. We therefore use
a special utility (`nltok`) to recognize the line break tokens, which
makes sure that the current line number is properly increased internally.

A quick note about the types: `L1 q Void 1 CSV0` describes a
lexer that operates on state thread `q` (you can ignore this part
for now), emits custom errors of type `Void`
(no custom errors in this case, because `Void` is uninhabited),
and emits bounded tokens of type `CSV0`. After every token, we
get a new state to start with of type `Index 1`, which is a
natural number (encoded as a value of type `Bits32`)
strictly less than 1. Again, we will see more about this when
we talk about context sensitive lexers.

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

csv1 : L1 q Void 1 CSV1
csv1 =
  lexer
    [ ctok ',' Comma1
    , nltok linebreak NL1
    , ctok "true" (Bool1 True)
    , ctok "false" (Bool1 False)
    , convTok (opt '-' >> decimal) (Int1 . integer)
    , readTok (plus (dot && not ',')) Txt1
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
or as a text token. In addition `"\r\n"` could be read as
one or two line breaks. Go ahead and check at the REPL
how `pretty` deals with these cases.

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

### Quoted Text

Currently, our CSV lexer cannot process any text that contains
commas. Likewise, it is not possible to include any control
characters such as tabs or line breaks in our text tokens.
We'd now like to add support for these.

Again, there are several strategies we could use here. What we are
going to do is to add support for quoted strings. This will allow
us to have text with commas by wrapping the corresponding text
in double quotes. However, a quoted
string can no longer contain double quote characters, so we need
a way to escape those. Likewise, we'd like to include and escape
some other characters such as tabs and line breaks.

Here's a regular expression for quoted strings:

```idris
quoted : RExp True
quoted = '"' >> star qchar >> '"'
  where
    qchar : RExp True
    qchar =
          (dot && not '"')
      <|> #""""#
      <|> #""n"#
      <|> #""r"#
      <|> #""t"#
```

With this, we can enhance our lexer:

```idris
unquote : ByteString -> String

csv1_2 : L1 q Void 1 CSV1
csv1_2 =
  lexer
    [ ctok ',' Comma1
    , nltok linebreak NL1
    , ctok "true" (Bool1 True)
    , ctok "false" (Bool1 False)
    , convTok (opt '-' >> decimal) (Int1 . integer)
    , readTok (plus (dot && not ',' && not '"')) Txt1
    , convTok quoted (Txt1 . unquote)
    ]
```

In order to keep things simple, we are going use character lists
to implement `unquote`:

```idris
unquote = go [<] . unpack . toString
  where
    go : SnocList Char -> List Char -> String
    go sc []              = pack (sc <>> [])
    go sc ('"'::'"' ::xs) = go (sc :< '"') xs
    go sc ('"'::'t' ::xs) = go (sc :< '\t') xs
    go sc ('"'::'n' ::xs) = go (sc :< '\n') xs
    go sc ('"'::'r' ::xs) = go (sc :< '\r') xs
    go sc ('"'::xs)       = go sc xs
    go sc (x::xs)         = go (sc :< x) xs
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
lexUQ : L1 q Void 1 String
lexUQ =
  lexer
    [ ctok #""""# "\""
    , ctok #""n"# "\n"
    , ctok #""r"# "\r"
    , ctok #""t"# "\t"
    , ctok #"""#  ""
    , readTok (plus (dot && not '"' && not '\\')) id
    ]

fastUnquote : ByteString -> String
fastUnquote bs =
  case parseBytes lexUQ Virtual bs of
    Left  _  => ""
    Right xs => fastConcat (map val xs)
```

## Under the Hood: Context-sensitive Lexers

In this section we are going to write a context-sensitive lexer.
The techniques we learn here are going to be used in the next section,
where we'll write a proper CSV-parser.

Before we continue, please note that ilex uses thread-local mutable
state to keep track of the parts we parsed so far. This makes use of
linear types and the [ref1 library](https://github.com/stefan-hoeck/idris2-ref1).
It is recommended that readers familiarize themselves with the
techniques described there in order to better understand what's
coming next.

### A Custom Mutable Parser Stack

We'd like to reimplement the behavior of `csv1_2` but without having to
read every quoted string token twice. In order to do this, we will already
have to implement a mini-parser, because we are going to use different
lexers, depending on whether we are currently
in a quoted string token or not.

```idris
0 QSTCK : Type -> Type
QSTCK = Stack Void (SnocList $ Bounded CSV1) 2
```

Parser stack `QSTCK q` is a wrapper around several mutable references
that can be manipulated in state-thread `q`.

### Parser State

Unlike simple lexers, which always operate in the same state, a proper
parser can be in one of several states, and each state expects and
recognizes different lexicographic tokens.

For our very simple context-sensitive lexer, we recognize two
states, so our state size is `2`:

```idris
QSz : Bits32
QSz = 2
```

Our lexer can be in one of two states: `0`, which is the default
state and is predefined as `Ini`, and `InStr`, which let's us know
that we are currently inside a quoted string token:

```idris
QST : Type
QST = Index QSz

InStr : QST
InStr = 1
```

As you can see, a parser state is just an index into an array of the
given size. In ilex, almost everything is array-backed for maximum
performance.

### Lexers

The next step is to define a lexer for each of the states our parser
can be in. For every token recognized by one of the lexers we not
only need to describe how the token affects our mutable parser stack,
but also return the state the parser will be in *after* the given token
was recognized. For the initial state, almost nothing changes
compared to `csv1_2`:

```idris
lexInit : DFA q 2 QSTCK
lexInit =
  dfa
    [ ctok ',' Comma1
    , nltok linebreak NL1
    , ctok "true" (Bool1 True)
    , ctok "false" (Bool1 False)
    , convTok (opt '-' >> decimal) (Int1 . integer)
    , readTok (plus (dot && not ',' && not '"')) Txt1
    , copen '"' (pure InStr)
    ]
```

*DFA* is an acronym for "discrete finite automaton", and utility `dfa`
converts a list of pairs (regular expressions plus state transformations)
to such an automaton.

As you can see, since `QSTCK` implements interfaces `LC` and `LexST`,
we can just reuse the utilities from the previous example. However,
we no longer recognize a whole quoted string but just the opening
quote. We use the `copen` utility, which will push the current
token bounds onto a stack of bounds of things that need to be closed.
Other than that, we just return the new parser state, which will
be `InStr`.

Once we are in a quoted string, we recognize escape sequences as
well as chunks of unescaped text. These will be appended to
the snoc list in the `strs` mutable reference. Once we encounter
an unescaped closing quote, we end quoted string recognition
and append the recognized, concatenated string to the list of tokens.

Here are the necessary utilities and token map:

```idris
closeStr : (x : QSTCK q) => F1 q QST

lexStr : DFA q QSz QSTCK
lexStr =
  dfa
    [ cexpr #""""# $ pushStr InStr "\""
    , cexpr #""n"# $ pushStr InStr "\n"
    , cexpr #""r"# $ pushStr InStr "\r"
    , cexpr #""t"# $ pushStr InStr "\t"
    , cexpr '"' closeStr
    , read (plus $ dot && not '"') (pushStr InStr)
    ]
```

Function `closeStr` is more involved: In this case, we need to manually
construct the token bounds, append the bounded token to the list of
recognized tokens, and change the parser state back to `Ini`:

```idris
closeStr = T1.do
  bs <- closeBounds
  s  <- getStr
  push1 x.stack_ (B (Txt1 s) bs)
  pure Ini
```

We now wrap up the different lexers in an array of lexers, which
describes the possible state transformations for every parser state.

```idris
quotedTrans : Lex1 q QSz QSTCK
quotedTrans = lex1 [E Ini lexInit, E InStr lexStr]
```

### Error Handling

To finalize our context-aware lexer, we need to generate proper
error messages. Again, the possible error messages are stored
in an array (one handler for each parser state). This is actually
quite nice, because it allows us to decouple the handling of errors
from the parser's state transformations. Whenever the current DFA
ends in an error state, the corresponding error handler is picked
from the array and passed the parser stack and byte sequence
parsed so far:

```idris
quotedErr : Arr32 QSz (QSTCK q -> F1 q (BoundedErr Void))
quotedErr = arr32 QSz (unexpected []) [E InStr $ unclosedIfEOI "\"" []]
```

We also need to describe what happens when we reach the end of input.
Here, we check if we are in a valid parser state (a CSV string can
end in any state except within a quoted string) and either produce
a result or fail with an error:

```idris
quotedEOI : QST -> QSTCK q -> F1 q (Either (BoundedErr Void) (List $ Bounded CSV1))
quotedEOI st x =
  case st == Ini of
    False => arrFail QSTCK quotedErr st x
    True  => getList x.stack_ >>= pure . Right
```

Finally, we wrap everything up in a record of type `P1` (a "linear parser").
We are going to have a look at the `lchunk` thing when we talk about
streaming large amounts of data:

```idris
csv1_3 : P1 q (BoundedErr Void) QSz QSTCK (List $ Bounded CSV1)
csv1_3 = P Ini (init [<]) quotedTrans snocChunk quotedErr quotedEOI
```

## Parsing CSV Files

We are now ready to learn how to properly parse comma separated values.
We use the same techniques as in the last section (a mutable parser stack
plus several parser states with corresponding state transformations).

However, instead of just listing the lexicographic tokens, we are going
to actually accumulate these tokens into a larger data structure. We therefore
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

Interpolation Line where interpolate = show

0 Table : Type
Table = List Line
```

As you can see, a CSV table is just a list of lines, with a line
consisting of a line number and a list of cells.

### Parser Stack and State

Below is the record of mutable references we are going to use to accumulate
lines: As usual, we include the fields for keeping track of
token bounds. In addition, we have mutable references for
accumulating quoted strings, the current line, and the whole
table. Typically, we call this the parser's *stack*, even though
it consists of more than a single (snoc)list:

```idris
public export
record CSTCK (q : Type) where
  constructor C
  line  : Ref q Nat
  col   : Ref q Nat
  psns  : Ref q (SnocList Position)
  strs  : Ref q (SnocList String)
  err   : Ref q (Maybe $ BoundedErr Void)
  cells : Ref q (SnocList Cell)
  lines : Ref q (SnocList Line)
  bytes : Ref q ByteString

export %inline
HasPosition CSTCK where
  line      = CSTCK.line
  col       = CSTCK.col
  positions = CSTCK.psns

export %inline
HasError CSTCK Void where
  error = err

export %inline
HasStringLits CSTCK where
  strings = strs

export %inline
HasStack CSTCK (SnocList Line) where
  stack = lines

export %inline
HasBytes CSTCK where
  bytes = CSTCK.bytes

export
cinit : F1 q (CSTCK q)
cinit = T1.do
  l  <- ref1 Z
  c  <- ref1 Z
  bs <- ref1 [<]
  ss <- ref1 [<]
  er <- ref1 Nothing
  cs <- ref1 [<]
  ls <- ref1 [<]
  by <- ref1 ""
  pure (C l c bs ss er cs ls by)
```

Next, we'll define the different parser states. We want to make
sure we add an empty `Null` cell in case we encounter two
consecutive commas or a comma followed by a line break. Also,
there must not be two consecutive values, and we want to know
whether we are currently parsing a quoted string or not. This
leads to four distinct parser states (the initial state `Ini`
marks the beginning of a line). However, we add one more state,
which will only be reached when we encounter an unescaped line break
inside a quoted string: In our case, this is interpreted as an error,
and we want to make sure that this error produces an error message
explaining that we have encountered an unclosed quote.

```idris
public export
CSz : Bits32
CSz = 5

public export
0 CST : Type
CST = Index CSz

export
Val, Str, Com, NL : CST
Val = 1; Str = 2; Com = 3; NL = 4
```

### State Transitions

We are now going to define the parser's state transitions:
The lexicographic tokens we recognize at each parser
state, how they affect the parser stack, and the parser
state *after* encountering a token.

First: After encountering a CSV cell, we push it onto the
`cells` stack and switch to the `Val` state, because
we just encountered a value:

```idris
onCell : (x : CSTCK q) => Cell ->F1 q CST
onCell v = push1 x.cells v >> pure Val
```

Second: After encountering a line break, we increase the line
number and assemble the CSV line from the current line number
and collected cells. If the list of cells is empty, we do not
append an empty line to the table.

There is one special case we have to consider: If the line
break occurred right after a comma, we make sure to push a
`Null` cell onto the stack of cells:

```idris
onNL : (x : CSTCK q) => (afterComma : Bool) -> F1 q CST
onNL afterComma = T1.do
  incline 1
  when1 afterComma (push1 x.cells Null)
  cs@(_::_) <- getList x.cells | [] => pure Ini
  ln <- read1 x.line
  push1 x.lines (L ln cs)
  pure Ini
```

With the above, we can already define the default lexer.
This comes with two additional state transitions that can
be given inline: After encountering a comma, we push an empty cell
onto the stack and switch to the `Com` state. Likewise,
after encountering a double quote, we *open* a new
thing that needs to be closed (`copen`) and switch to
the `Str` state:

```idris
csvDflt : (afterComma : Bool) -> DFA q CSz CSTCK
csvDflt afterComma =
  dfa
    [ cexpr ',' $ push1 (cells %search) Null >> pure Com
    , conv linebreak (\_ => onNL afterComma)
    , cexpr "true" $ onCell (CBool True)
    , cexpr "false" $ onCell (CBool False)
    , conv (opt '-' >> decimal) (onCell . CInt . integer)
    , read (plus $ dot && not ',' && not '"') (onCell . CStr)
    , copen '"' (pure Str)
    ]
```

The string lexer pushes all encountered text regions and escape
sequences onto the corresponding stack until a closing
double quote is encountered, which leads to the accumulated
string to be pushed onto the stack of cells (`onCell`).

```idris
csvStr : DFA q CSz CSTCK
csvStr =
  dfa
    [ cexpr #""""# $ pushStr Str "\""
    , cexpr #""n"# $ pushStr Str "\n"
    , cexpr #""r"# $ pushStr Str "\r"
    , cexpr #""t"# $ pushStr Str "\t"
    , cclose '"' $ getStr >>= onCell . CStr
    , read (plus $ dot && not '"') $ pushStr Str
    , conv linebreak (const $ pure NL)
    ]
```

Please note the special handling of a line break inside a quoted string:
We immediately switch to the `NL` state, which, as we will see in a moment,
comes without any valid state transformations and thus will automatically
lead to an error being raised.

Finally, we gather the state transformations for every parser state
in an array of transformations (since the `NL` is always invalid, we
don't have to provide an automaton of state transformations to it:
it will automatically be given the empty automaton that always fails):

```idris
csvSteps : Lex1 q CSz CSTCK
csvSteps =
  lex1
    [ E Ini (csvDflt False)
    , E Val $ dfa [cexpr ',' (pure Com), conv linebreak (const $ onNL False)]
    , E Str csvStr
    , E Com (csvDflt True)
    ]
```

### Finalizing the Parser

The only thing missing is error handling and the final assembling of
the parser. States `Str`, `Val`, and `NL` throw custom errors:

```idris
csvErr : Arr32 CSz (CSTCK q -> F1 q (BoundedErr Void))
csvErr =
  arr32 CSz (unexpected [])
    [ E Str $ unclosedIfEOI "\"" []
    , E Val $ unexpected [","]
    , E NL  $ unclosed "\""
    ]

csvEOI : CST -> CSTCK q -> F1 q (Either (BoundedErr Void) Table)
csvEOI st x =
  case st == Str || st == NL of
    True  => arrFail CSTCK csvErr st x
    False => T1.do
      _   <- onNL (st == Com)
      tbl <- getList x.lines
      pure (Right tbl)
```

And here's the final CSV parser:

```idris
csv : P1 q (BoundedErr Void) CSz CSTCK Table
csv = P Ini cinit csvSteps snocChunk csvErr csvEOI
```

A quick note about the `snocChunk` part: Since the parsers
and lexers in this library maintain their own internal stack, they can
be used directly to stream large amounts of data via the
*ilex-streams* library (see below). Every time a chunk of bytes as
been loaded into memory and consumed by the streaming run loop,
the values accumulated so far should be emitted and removed from
the parser stack to release the memory they consumed. This is done
via field `P1.chunk`. In our case, we use utility `snocChunk` to
simply extract and emit the contents of a mutable snoc list.

With all this said and done, here's a small CSV string that can be
used to test our parser:

```idris
csvStr3 : String
csvStr3 =
  #"""
  entry 1,"this is a ""test""",true,12
  entry 2,"below is an empty line",false,0

  entry 3,"this one has an empty cell",,-20
  entry 4,"finally, a linebreak: "r"n",true,4
  entry 5,"next one is almost empty",true,18
  ,,,
  """#
```

Below are a couple of erroneous CSV strings. Feel free to
run our parser against those and check out the error messages
we get:

```idris
twoValues : String
twoValues = "this is wrong,\"foo\"false"

invalidTab : String
invalidTab = "this is wrong,foo,false,\"Ups: \t\",bar"

unclosedQuote : String
unclosedQuote = "this is wrong,foo,false,\"Ups , bar"
```

The error message from the last example is important: Instead
of complaining about having reached the end of input (which, in
my opinion, would be rather unspecific), we mark the opening
quote that has not been properly closed.

We'd like to do the same in case we arrive at a line break
in the middle of a quoted string. Again, the resulting error
message will be more specific. This is only possible by
including the line break state `NL` as one of the states
reachable from the quoted string lexer.
Here's an example where this is
relevant. Feel free to remove the `linebreak` line from
the definition of `csvStr` and re-check the parser's behavior
at the REPL.

```idris
unclosedMultiline : String
unclosedMultiline =
  """
  foo,"this is a,12
  bar,test,13
  """
```

## Streaming Files

Functions such as `parse` and `parseString` are supposed to process a
(byte)string as a whole, so the whole data needs to fit into memory.
Sometimes, however, we would like to process huge amounts of data.
Package *ilex-streams*, which is also part of this project, provides
utilities for this occasion. Fortunately, data type `P1` already
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
0 Prog : Type -> Type -> Type
Prog o r = AsyncPull Poll o [ParseError Void, Errno] r

covering
runProg : Prog Void () -> IO ()
runProg prog =
 let handled := handle [stderrLn . interpolate, stderrLn . interpolate] prog
  in epollApp $ mpull handled
```

If the above is foreign to you, please work through the tutorials
provided with the *async* and *streams* libraries.

And here's an example how to stream a single, possibly huge, CSV file
(this will print the total number of non-empty CSV-lines encountered):

```idris
streamCSV : String -> Prog Void ()
streamCSV pth =
     readBytes pth
  |> streamParse csv (FileSrc pth)
  |> C.count
  |> printLnTo Stdout
```

Functions `readBytes`, `C.count`, and `printLnTo` are just standard
streaming utilities, while function `streamParse` is provided by
the *ilex-streams* library. With the above, you can stream arbitrarily
large CSV files in constant memory.

However, there are some minor differences compared to tokenizing whole
strings of data:

For obvious reasons, we don't store the whole byte stream in memory,
so error messages will only contain the region (start and end line and
column) where the error occurred but not a highlighted excerpt of the
string with the error.

```idris
streamCSVFiles : Prog String () -> Prog Void ()
streamCSVFiles pths =
     flatMap pths (\p => readBytes p |> streamParse csv (FileSrc p))
  |> C.count
  |> printLnTo Stdout
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
covering
main : IO ()
main = runProg $ streamCSVFiles (P.tail args)
```

In order to compile this and check it against your own
CSV files:

```sh
pack -o csv exec examples/src/README.md
examples/build/exec/csv ~/downloads/*.csv
```

<!-- vi: filetype=idris2:syntax=markdown
-->

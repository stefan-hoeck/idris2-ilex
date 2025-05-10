module Text.ILex.FS

import public FS
import public Text.ILex

%default total

lexFrom :
     (l : Lexer a)
  -> LexState l.states
  -> (pos : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> LexRes l.states a

||| Operates a lexer on a chunk of bytes returning
||| starting from the given lexer state.
|||
||| This is the most general form, allowing us to
||| begin and stop in the middle of a token, which
||| is important for streaming.
export %inline
lexChunk :
     (l : Lexer a)
  -> LexState l.states
  -> (n ** IBuffer n)
  -> LexRes l.states a
lexChunk l s (n ** buf) = lexFrom l s n buf

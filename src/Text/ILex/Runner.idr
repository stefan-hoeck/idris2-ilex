module Text.ILex.Runner

import Data.Buffer
import Text.ILex.Internal.Runner
import public Text.ParseError
import public Text.FC
import public Text.ILex.Parser

%default total

||| Tries to parse a byte vector into a value.
export
run : {n : _} -> Parser1 e a -> IBuffer n -> Either e a

||| Like `run` but processes a UTF-8 string instead.
export %inline
runString : Parser1 e a -> String -> Either e a
runString l s = run l (fromString s)

||| Like `run` but processes a `ByteString` instead.
export %inline
runBytes : Parser1 e a -> ByteString -> Either e a
runBytes l (BS s bv) = run l (toIBuffer bv)

||| Like `run` but processes a `ByteString` instead.
export
runList : Parser1 e a -> List ByteString -> Either e a

||| Like `run` but fails with a proper parse error
||| including error bounds and highlighting of
||| the section where an error occurred.
export %inline
parse :
     {n : _}
  -> Parser1 (BBErr e) a
  -> Origin
  -> IBuffer n
  -> Either (ParseError e) a
parse l o buf = mapFst (toParseError o (toString buf 0 n)) (run l buf)

||| Like `parse` but processes a UTF-8 string instead.
export %inline
parseString :
     Parser1 (BBErr e) a
  -> Origin
  -> String
  -> Either (ParseError e) a
parseString l o s = parse l o (fromString s)

||| Like `parse` but processes a `ByteString` instead.
export %inline
parseBytes :
     Parser1 (BBErr e) a
  -> Origin
  -> ByteString
  -> Either (ParseError e) a
parseBytes l o bs = mapFst (toParseError o (toString bs)) (runBytes l bs)

--------------------------------------------------------------------------------
-- Lexer run loop
--------------------------------------------------------------------------------

||| Lexing state.
|||
||| This encapsulates the current state as well as
||| the remainder of the previous chunk that marks
||| the beginning of the current token.
public export
record LexState (p : P1 q e a) where
  constructor LST
  {0 sts  : Nat}
  state   : PIx p
  stack   : PST p
  dfa     : PStepper sts p
  cur     : PByteStep sts p
  tok     : Maybe (PStep p)

export
init : (p : P1 q e a) -> F1 q (LexState p)
init p t =
 let stck # t := p.stck t
     L _ dfa  := p.lex `at` p.init
  in LST p.init stck dfa (dfa `at` 0) Nothing # t

||| Result of a partial lexing step: In such a step, we lex
||| till the end of a chunk of bytes, allowing for a remainder of
||| bytes that could not yet be identified as a tokens.
public export
0 LoopRes : (p : P1 q e a) -> Type
LoopRes p = F1 q (Either e (LexState p))

export
lastStep : (p : P1 q e a) -> LexState p -> F1 q (Either e a)
lastStep p (LST st sk _ _ tok) t =
  case tok of
    Nothing => case getBytes @{p.hasb} t of
      BS 0 _ # t => p.eoi st sk t
      _      # t => fail p st sk t
    Just f  =>
     let st2 # t := f.run st sk t
         l   # t := read1 (len @{p.hasb} sk) t
         _   # t := mod1 (relpos @{p.hasb} sk) (+ cast l) t
      in p.eoi st2 sk t

parameters {0 q,e,a : Type}
           {0 n     : Nat}
           (parser  : P1 q e a)
           (stck    : PST parser)
           (buf     : IBuffer n)
           (rel     : Ref q Integer)
           (len     : Ref q Nat)

  %inline
  endChunk : Nat -> F1' q
  endChunk l t =
   let _  # t := write1 len l t
       bs # t := getBytes @{parser.hasb} t
       cr # t := read1 (cur @{parser.hasb} stck) t
       _  # t := write1 (cur @{parser.hasb} stck) "" t
       _  # t := write1 (prev @{parser.hasb} stck) bs t
       _  # t := mod1 (offset @{parser.hasb} stck) (+ cr.size) t
    in write1 rel (negate $ cast bs.size) t

  %inline
  stp : PIx parser -> PStep parser -> Nat -> F1 q (PIx parser)
  stp st f l t =
    let _ # t := write1 len l t
        r # t := f.run st stck t
        _ # t := mod1 rel (+ cast l) t
     in r # t

  step :
       (st          : PIx parser)
    -> (dfa         : PStepper k parser)
    -> (cur         : PByteStep k parser)
    -> (len         : Nat)
    -> (pos         : Nat)
    -> {auto x      : Ix pos n}
    -> LoopRes parser

  succ :
       (st          : PIx parser)
    -> (dfa         : PStepper k parser)
    -> (cur         : PByteStep k parser)
    -> (last        : PStep parser)
    -> (len         : Nat)
    -> (pos         : Nat)
    -> {auto x      : Ix pos n}
    -> LoopRes parser

  loop : (st : PIx parser) -> (pos : Nat) -> (x : Ix pos n) => LoopRes parser
  loop st 0     t =
   let _ # t   := endChunk 0 t
       L _ dfa := parser.lex `at` st
    in Right (LST st stck dfa (dfa `at` 0) Nothing) # t
  loop st (S k) t =
   let L _ dfa := parser.lex `at` st
       cur     := dfa `at` 0
    in case cur `atByte` (buf `ix` k) of
         Done f     =>
          let s2 # t := stp st f 1 t
           in loop s2 k t
         Move   nxt f => succ st dfa (dfa `at` nxt) f   1 k t
         MoveE  nxt   => step st dfa (dfa `at` nxt)     1 k t
         _            =>
          let _ # t := write1 len 1 t
           in fail parser st stck t

  succ st dfa cur f l 0     t =
   let _ # t := endChunk l t
    in Right (LST st stck dfa cur (Just f)) # t
  succ st dfa cur f l (S k) t =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => succ st dfa cur f (S l) k t
         Done f       =>
          let s2 # t := stp st f (S l) t
           in loop s2 k t
         Move   nxt f => succ st dfa (dfa `at` nxt) f (S l) k t
         MoveE  nxt   => step st dfa (dfa `at` nxt)   (S l) k t
         Bottom       =>
          let s2 # t := stp st f l t
           in loop s2 (S k) t

  step st dfa cur l 0     t =
   let _ # t := endChunk l t
    in Right (LST st stck dfa cur Nothing) # t
  step st dfa cur l (S k) t =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => step st dfa cur l k t
         Done f       =>
          let s2 # t := stp st f (S l) t
           in loop s2 k t
         Move   nxt f => succ st dfa (dfa `at` nxt) f (S l) k t
         MoveE  nxt   => step st dfa (dfa `at` nxt)   (S l) k t
         Bottom       =>
          let _ # t := write1 len (S l) t
           in fail parser st stck t

export
stepState :
     {n : Nat}
  -> IBuffer n
  -> (p : P1 q e a)
  -> LexState p
  -> LoopRes p
stepState {n = 0}   buf p lst t = Right lst # t
stepState {n = S k} buf p (LST st sk dfa cr tok) t =
 let byte  := at buf 0
     rrel  := relpos @{p.hasb} sk
     rlen  := len @{p.hasb} sk
     l # t := read1 rlen t
     _ # t := write1 (cur @{p.hasb} sk) (fromIBuffer buf) t
  in case cr `atByte` byte of
       Keep         => case tok of
         Just f  => succ p sk buf rrel rlen st dfa cr f (S l) k t
         Nothing => step p sk buf rrel rlen st dfa cr   (S l) k t
       Done f       =>
        let s2 # t := stp p sk buf rrel rlen st f (S l) t
         in loop p sk buf rrel rlen s2 k t
       Move   nxt f => succ p sk buf rrel rlen st dfa (dfa `at` nxt) f (S l) k t
       MoveE  nxt   => step p sk buf rrel rlen st dfa (dfa `at` nxt)   (S l) k t
       Bottom     => case tok of
         Just f  =>
          let s2 # t := stp p sk buf rrel rlen st f l t
           in loop p sk buf rrel rlen s2 (S k) t
         Nothing =>
          let _ # t := write1 rlen (S l) t
           in fail p st sk t

run p buf =
 run1 $ \t =>
   let lst        # t := Runner.init p t
       Right lst2 # t := stepState buf p lst t | Left x # t => Left x # t
    in lastStep p lst2 t

loopAll : (p : P1 q e a) -> LexState p -> List ByteString -> F1 q (Either e a)
loopAll p lst []              t = lastStep p lst t
loopAll p lst (BS n bv :: xs) t =
  case stepState (toIBuffer bv) p lst t of
    Left x     # t => Left x # t
    Right lst2 # t => loopAll p lst2 xs t

runList p bs =
  run1 $ \t => let lst # t := Runner.init p t in loopAll p lst bs t


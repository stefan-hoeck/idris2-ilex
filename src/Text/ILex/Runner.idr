module Text.ILex.Runner

import Data.Buffer
import Text.ILex.Internal.Runner
import public Text.ParseError
import public Text.FC
import public Text.ILex.Parser
import public Text.ILex.Interfaces

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
  tok     : PStep p

export
init : (n : Nat) -> IBuffer n -> (p : P1 q e a) -> F1 q (LexState p)
init n buf p t =
 let stck # t := p.stck n buf t
     L _ dfa  := p.lex `at` p.init
  in LST p.init stck dfa (dfa `at` 0) Err # t

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
    Err => case getBytes @{p.hasb} t of
      BS 0 _ # t => p.eoi st sk t
      _      # t => fail p st sk t
    Run f =>
     let st2 # t := f (E sk t)
         _   # t := toFinalPos @{p.hasb} t
      in p.eoi st2 sk t
    Ign   =>
     let _   # t := toFinalPos @{p.hasb} t
      in p.eoi st sk t

parameters {0 q,e,a : Type}
           {0 n     : Nat}
           (parser  : P1 q e a)
           (sk      : PST parser)
           (buf     : IBuffer n)
           (rfrom   : Ref q (LTENat n))
           (rtill   : Ref q (LTENat n))

  %inline
  stp : Fun1 q parser.state x -> (0 till : Nat) -> Ix till n => F1 q x
  stp f till t =
    let _ # t := write1 rtill (lteNat till) t
     in f (E sk t)

  step :
       (st          : PIx parser)
    -> (dfa         : PStepper k parser)
    -> (cur         : PByteStep k parser)
    -> (pos         : Nat)
    -> {auto posIx  : Ix pos n}
    -> LoopRes parser

  succ :
       (st          : PIx parser)
    -> (dfa         : PStepper k parser)
    -> (cur         : PByteStep k parser)
    -> (last        : PRun parser)
    -> (pos         : Nat)
    -> {auto posIx  : Ix pos n}
    -> LoopRes parser

  igno :
       (st          : PIx parser)
    -> (dfa         : PStepper k parser)
    -> (cur         : PByteStep k parser)
    -> (pos         : Nat)
    -> {auto posIx  : Ix pos n}
    -> LoopRes parser

  loop : (st : PIx parser) -> (pos : Nat) -> (x : Ix pos n) => LoopRes parser
  loop st 0     t =
   let _ # t   := write1 rfrom (lteNat 0) t
       _ # t   := write1 rtill (lteNat 0) t
       L _ dfa := parser.lex `at` st
    in Right (LST st sk dfa (dfa `at` 0) Err) # t
  loop st (S k) t =
   let _ # t   := write1 rfrom (lteNat $ S k) t
       L _ dfa := parser.lex `at` st
       cur     := dfa `at` 0
    in case cur `atByte` (buf `ix` k) of
         Done f       => let s2 # t := stp f k t in loop s2 k t
         Ignore       => loop st k t
         Move   nxt f => succ st dfa (dfa `at` nxt) f k t
         MoveI  nxt   => igno st dfa (dfa `at` nxt)   k t
         MoveE  nxt   => step st dfa (dfa `at` nxt)   k t
         _            => stp (failFun1 parser st) k t

  succ st dfa cur f 0     t =
   let _ # t := write1 rtill (lteNat 0) t
    in Right (LST st sk dfa cur (Run f)) # t
  succ st dfa cur f (S k) t =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => succ st dfa cur f k t
         Done f       => let s2 # t := stp f k t in loop s2 k t
         Ignore       => loop st k t
         Move   nxt f => succ st dfa (dfa `at` nxt) f k t
         MoveI  nxt   => igno st dfa (dfa `at` nxt)   k t
         MoveE  nxt   => step st dfa (dfa `at` nxt)   k t
         Bottom       => let s2 # t := stp f (S k) t in loop s2 (S k) t

  igno st dfa cur 0     t =
   let _ # t := write1 rtill (lteNat 0) t
    in Right (LST st sk dfa cur Ign) # t
  igno st dfa cur (S k) t =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => igno st dfa cur   k t
         Done f       => let s2 # t := stp f k t in loop s2 k t
         Ignore       => loop st k t
         Move   nxt f => succ st dfa (dfa `at` nxt) f k t
         MoveI  nxt   => igno st dfa (dfa `at` nxt)   k t
         MoveE  nxt   => step st dfa (dfa `at` nxt)   k t
         Bottom       => loop st (S k) t

  step st dfa cur 0     t =
   let _ # t := write1 rtill (lteNat 0) t
    in Right (LST st sk dfa cur Err) # t
  step st dfa cur (S k) t =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => step st dfa cur k t
         Done f       => let s2 # t := stp f k t in loop s2 k t
         Ignore       => loop st k t
         Move   nxt f => succ st dfa (dfa `at` nxt) f k t
         MoveI  nxt   => igno st dfa (dfa `at` nxt)   k t
         MoveE  nxt   => step st dfa (dfa `at` nxt)   k t
         Bottom       => stp (failFun1 parser st) k t

export
stepState :
     {n : Nat}
  -> IBuffer n
  -> (p : P1 q e a)
  -> LexState p
  -> LoopRes p
stepState {n = 0}   buf p lst t = Right lst # t
stepState {n = S k} buf p (LST st skOld dfa cr tok) t =
 let bs   # t := getBytes @{p.hasb} @{skOld} t
     BP o # t := startPos {hb = p.hasb, sk = skOld} t
     rf   # t := ref1 (first $ S k) t
     rt   # t := ref1 (first $ S k) t
     sk       := Parser.copy @{p.hasb} (S k) o bs buf rf rt skOld
     byte     := at buf 0
  in case cr `atByte` byte of
       Keep         => case tok of
         Run f  => succ p sk buf rf rt st dfa cr f k t
         Ign    => igno p sk buf rf rt st dfa cr   k t
         Err    => step p sk buf rf rt st dfa cr   k t
       Done f       =>
        let s2 # t := stp p sk buf rf rt f k t
         in loop p sk buf rf rt s2 k t
       Ignore       => loop p sk buf rf rt st k t
       Move   nxt f => succ p sk buf rf rt st dfa (dfa `at` nxt) f k t
       MoveI  nxt   => igno p sk buf rf rt st dfa (dfa `at` nxt)   k t
       MoveE  nxt   => step p sk buf rf rt st dfa (dfa `at` nxt)   k t
       Bottom     => case tok of
         Run f  =>
          let s2 # t := stp p sk buf rf rt f (S k) t
              ske    := Parser.copy @{p.hasb} (S k) (o+bs.size) empty buf rf rt sk
           in loop p ske buf rf rt s2 (S k) t
         Ign    =>
          let ske    := Parser.copy @{p.hasb} (S k) (o+bs.size) empty buf rf rt sk
           in loop p ske buf rf rt st (S k) t
         Err => stp p sk buf rf rt (failFun1 p st) k t

run p buf =
 run1 $ \t =>
   let lst        # t := Runner.init n buf p t
       Right lst2 # t := stepState buf p lst t | Left x # t => Left x # t
    in lastStep p lst2 t

loopAll : (p : P1 q e a) -> LexState p -> List ByteString -> F1 q (Either e a)
loopAll p lst []              t = lastStep p lst t
loopAll p lst (BS n bv :: xs) t =
  case stepState (toIBuffer bv) p lst t of
    Left x     # t => Left x # t
    Right lst2 # t => loopAll p lst2 xs t

runList p bs =
  run1 $ \t =>
   let lst # t := Runner.init 0 empty p t
    in loopAll p lst bs t

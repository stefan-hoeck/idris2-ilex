module Text.ILex.Dependent.Runner

import Data.Buffer
import public Text.ParseError
import public Text.FC
import public Text.ILex.Dependent.Parser

%default total

||| Tries to parse a byte vector into a value.
export
run : {n : _} -> IParser e a -> IBuffer n -> Either e a

||| Like `run` but processes a UTF-8 string instead.
export %inline
runString : IParser e a -> String -> Either e a
runString l s = run l (fromString s)

||| Like `run` but processes a `ByteString` instead.
export %inline
runBytes : IParser e a -> ByteString -> Either e a
runBytes l (BS s bv) = run l (toIBuffer bv)

||| Like `run` but processes a `ByteString` instead.
export
runList : IParser e a -> List ByteString -> Either e a

||| Like `run` but fails with a proper parse error
||| including error bounds and highlighting of
||| the section where an error occurred.
export %inline
parse :
     {n : _}
  -> IParser (BBErr e) a
  -> Origin
  -> IBuffer n
  -> Either (ParseError e) a
parse l o buf = mapFst (toParseError o (toString buf 0 n)) (run l buf)

||| Like `parse` but processes a UTF-8 string instead.
export %inline
parseString :
     IParser (BBErr e) a
  -> Origin
  -> String
  -> Either (ParseError e) a
parseString l o s = parse l o (fromString s)

||| Like `parse` but processes a `ByteString` instead.
export %inline
parseBytes :
     IParser (BBErr e) a
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
record LexState (p : IParser e a) where
  constructor LST
  {0 sts      : Nat}
  {0 ltpe     : Type}
  lexer       : p.lexer ltpe
  stack       : In ltpe
  dfa         : PMachine sts p ltpe
  cur         : PByteTrans sts p ltpe
  tok         : PStep p ltpe

export
init : {n : _} -> IBuffer n -> (p : IParser e a) -> LexState p
init buf p =
 let sk := I (Bytes.init buf) (first n) (first n) p.istack
     L _ dfa := at @{p.en} p.lex  p.init
  in LST p.init sk dfa (dfa `at` 0) Err

||| Result of a partial lexing step: In such a step, we lex
||| till the end of a chunk of bytes, allowing for a remainder of
||| bytes that could not yet be identified as a tokens.
public export
0 LoopRes : (p : IParser e a) -> Type
LoopRes p = Either e (LexState p)

export
lastStep : (p : IParser e a) -> LexState p -> Either e a
lastStep p (LST st sk _ _ tok) =
  case tok of
    Err => case getBytes sk of
      BS 0 _ => eoi p st sk
      _      => failI p st sk
    Run f => let E st2 k2 := f sk in eoi p st2 (toFinalPos' sk.bytes k2)
    Ign   => eoi p st (toFinalPos sk)

parameters {0 e,a : Type}
           {0 n   : Nat}
           (p     : IParser e a)
           (bs    : Bytes n)
           (buf   : IBuffer n)

  %inline
  stp :
       (0 st   : p.lexer t)
    -> (sk     : t)
    -> (f      : In t -> x)
    -> (from   : LTENat n)
    -> (0 till : Nat)
    -> {auto pix : Ix till n}
    -> x
  stp st sk f from till = f (I bs from (lteNat till) sk)

  step :
       (st          : p.lexer t)
    -> (sk          : t)
    -> (dfa         : PMachine k p t)
    -> (cur         : PByteTrans k p t)
    -> (from        : LTENat n) 
    -> (pos         : Nat)
    -> {auto posIx  : Ix pos n}
    -> LoopRes p

  succ :
       (st          : p.lexer t)
    -> (sk          : t)
    -> (dfa         : PMachine k p t)
    -> (cur         : PByteTrans k p t)
    -> (last        : PRun p t)
    -> (from        : LTENat n) 
    -> (pos         : Nat)
    -> {auto posIx  : Ix pos n}
    -> LoopRes p

  igno :
       (st          : p.lexer t)
    -> (sk          : t)
    -> (dfa         : PMachine k p t)
    -> (cur         : PByteTrans k p t)
    -> (from        : LTENat n) 
    -> (pos         : Nat)
    -> {auto posIx  : Ix pos n}
    -> LoopRes p

  loop :
       (st : p.lexer t)
    -> (sk : t)
    -> (pos : Nat)
    -> {auto x : Ix pos n}
    -> LoopRes p
  loop st sk 0     =
   let cs := I bs (lteNat 0) (lteNat 0) sk
       L _ dfa := at @{p.en} p.lex st
    in Right (LST st cs dfa (dfa `at` 0) Err)
  loop st sk (S k) =
   let from    := lteNat $ S k
       L _ dfa := at @{p.en} p.lex st
       cur     := dfa `at` 0
    in case cur `atByte` (buf `ix` k) of
         Done f       => let E s2 k2 := stp st sk f from k in loop s2 k2 k
         Ignore       => loop st sk k
         Move   nxt f => succ st sk dfa (dfa `at` nxt) f from k
         MoveI  nxt   => igno st sk dfa (dfa `at` nxt)   from k
         MoveE  nxt   => step st sk dfa (dfa `at` nxt)   from k
         _            => stp st sk (failI p st) from k

  succ st sk dfa cur f from 0     =
   let cs := I bs from (lteNat 0) sk
    in Right (LST st cs dfa cur (Run f))
  succ st sk dfa cur f from (S k) =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => succ st sk dfa cur f from k
         Done f       => let E s2 k2 := stp st sk f from k in loop s2 k2 k
         Ignore       => loop st sk k
         Move   nxt f => succ st sk dfa (dfa `at` nxt) f from k
         MoveI  nxt   => igno st sk dfa (dfa `at` nxt)   from k
         MoveE  nxt   => step st sk dfa (dfa `at` nxt)   from k
         Bottom       => let E s2 k2 := stp st sk f from (S k) in loop s2 k2 (S k)

  igno st sk dfa cur from 0     =
   let cs := I bs from (lteNat 0) sk
    in Right (LST st cs dfa cur Ign)
  igno st sk dfa cur from (S k) =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => igno st sk dfa cur   from k
         Done f       => let E s2 k2 := stp st sk f from k in loop s2 k2 k
         Ignore       => loop st sk k
         Move   nxt f => succ st sk dfa (dfa `at` nxt) f from k
         MoveI  nxt   => igno st sk dfa (dfa `at` nxt)   from k
         MoveE  nxt   => step st sk dfa (dfa `at` nxt)   from k
         Bottom       => loop st sk (S k)

  step st sk dfa cur from 0     =
   let cs := I bs from (lteNat 0) sk
    in Right (LST st cs dfa cur Err)
  step st sk dfa cur from (S k) =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => step st sk dfa cur from k
         Done f       => let E s2 k2 := stp st sk f from k in loop s2 k2 k
         Ignore       => loop st sk k
         Move   nxt f => succ st sk dfa (dfa `at` nxt) f from k
         MoveI  nxt   => igno st sk dfa (dfa `at` nxt)   from k
         MoveE  nxt   => step st sk dfa (dfa `at` nxt)   from k
         Bottom       => stp st sk (failI p st) from k

export partial
stepState : {n : _} -> IBuffer n -> (p : IParser e a) -> LexState p -> LoopRes p
stepState {n = 0}   buf p lst = Right lst
stepState {n = S k} buf p (LST st sk dfa cr tok) =
 let bs   := getBytes sk
     BP o := startPos sk
     rf   := first $ S k
     bts  := newBytes o bs buf
     byte := at buf 0
  in case cr `atByte` byte of
       Keep         => case tok of
         Run f  => succ p bts buf st sk.val dfa cr f rf k
         Ign    => igno p bts buf st sk.val dfa cr   rf k
         Err    => step p bts buf st sk.val dfa cr   rf k
       Done f       =>
        let E s2 k2 := stp p bts buf st sk.val f rf k
         in loop p bts buf s2 k2 k
       Ignore       => loop p bts buf st sk.val k
       Move   nxt f => succ p bts buf st sk.val dfa (dfa `at` nxt) f rf k
       MoveI  nxt   => igno p bts buf st sk.val dfa (dfa `at` nxt)   rf k
       MoveE  nxt   => step p bts buf st sk.val dfa (dfa `at` nxt)   rf k
       Bottom     => case tok of
         Run f  =>
          let E s2 k2 := stp p bts buf st sk.val f rf (S k)
              bts2            := newBytes (o+bs.size) empty buf
           in loop p bts2 buf s2 k2 (S k)
         Ign    =>
          let bts2            := newBytes (o+bs.size) empty buf
           in loop p bts2 buf st sk.val (S k)
         Err => stp p bts buf st sk.val (failI p st) rf k

run p buf =
  let lst        := Runner.init buf p
      Right lst2 := stepState buf p lst | Left x => Left x
   in lastStep p lst2

loopAll : (p : IParser e a) -> LexState p -> List ByteString -> Either e a
loopAll p lst []              = lastStep p lst
loopAll p lst (BS n bv :: xs) =
  case stepState (toIBuffer bv) p lst of
    Left x     => Left x
    Right lst2 => loopAll p lst2 xs

runList p bs = let lst := Runner.init empty p in loopAll p lst bs

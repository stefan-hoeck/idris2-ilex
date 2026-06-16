module Text.ILex.Runner

import Data.Buffer
import Text.ILex.Internal.Runner
import public Text.ParseError
import public Text.FC
import public Text.ILex.Parser

%default total

runFrom :
     {n      : Nat}
  -> (l      : Parser1 e a)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> Either e a

||| Tries to parse a byte vector into a value.
export %inline
run : {n : _} -> Parser1 e a -> IBuffer n -> Either e a
run l buf = runFrom l n buf

||| Like `run` but processes a UTF-8 string instead.
export %inline
runString : Parser1 e a -> String -> Either e a
runString l s = run l (fromString s)

||| Like `run` but processes a `ByteString` instead.
export
runBytes : Parser1 e a -> ByteString -> Either e a
runBytes l (BS s $ BV buf off lte) =
  runFrom l s {x = offsetToIx off} (take (off+s) buf)

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


parameters {0 q,e,a : Type}
           {0 n     : Nat}
           (parser  : P1 q e a)
           (stck    : PST parser)
           (buf     : IBuffer n)
           (pos     : Ref q BytePos)
           (len     : Ref q Nat)

  %inline
  end : Nat -> F1 q ()
  end l t = write1 len l t

  %inline
  stp : PIx parser -> PStep parser -> (0 p : _) -> (x : Ix p n) => Nat -> F1 q (PIx parser)
  stp st f p n t =
    let _ # t := end n t
        r # t := f.run st stck t
        _ # t := write1 pos (BP $ ixToNat x) t
     in r # t

  step :
       (st          : PIx parser)
    -> (dfa         : PStepper k parser)
    -> (cur         : PByteStep k parser)
    -> (len         : Nat)
    -> (pos         : Nat)
    -> {auto x      : Ix pos n}
    -> F1 q (Either e a)

  succ :
       (st          : PIx parser)
    -> (dfa         : PStepper k parser)
    -> (cur         : PByteStep k parser)
    -> (last        : PStep parser)
    -> (len         : Nat)
    -> (pos         : Nat)
    -> {auto x      : Ix pos n}
    -> F1 q (Either e a)

  loop : (st : PIx parser) -> (pos : Nat) -> (x : Ix pos n) => F1 q (Either e a)
  loop st 0     t = let _ # t := end 0 t in parser.eoi st stck t
  loop st (S k) t =
   let L _ dfa := parser.lex `at` st
       cur     := dfa `at` 0
    in case cur `atByte` (buf `ix` k) of
         Done f     =>
          let s2 # t := stp st f k 1 t
           in loop s2 k t
         Move   nxt f => succ st dfa (dfa `at` nxt) f   1 k t
         MoveE  nxt   => step st dfa (dfa `at` nxt)     1 k t
         _            => let _ # t := end 1 t in fail parser st stck t

  succ st dfa cur f len 0     t =
    ?lststp -- lastStep parser f st (toBS buf len 0) stck t
  succ st dfa cur f len (S k) t =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => succ st dfa cur f (S len) k t
         Done f       =>
          let s2 # t := stp st f k (S len) t
           in loop s2 k t
         Move   nxt f => succ st dfa (dfa `at` nxt) f (S len) k t
         MoveE  nxt   => step st dfa (dfa `at` nxt)   (S len) k t
         Bottom       =>
          let s2 # t := stp st f (S k) len t
           in loop s2 (S k) t

  step st dfa cur len 0     t =
   let _ # t := end len t
    in fail parser st stck t
  step st dfa cur len (S k) t =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => step st dfa cur len k t
         Done f       =>
          let s2 # t := stp st f k (S len) t
           in loop s2 k t
         Move   nxt f => succ st dfa (dfa `at` nxt) f (S len) k t
         MoveE  nxt   => step st dfa (dfa `at` nxt)   (S len) k t
         Bottom       =>
          let _ # t := end (S len) t
           in fail parser st stck t
--
-- runFrom p pos buf = run1 (go p)
--   where
--     go : P1 q e a -> F1 q (Either e a)
--     go p t =
--      let x # t := stck p t
--       in loop p x buf p.init pos t

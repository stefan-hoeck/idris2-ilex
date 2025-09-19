module Text.ILex.Runner

import Data.Buffer
import Text.ILex.Internal.Runner
import public Text.ParseError
import public Text.FC
import public Text.ILex.Parser

%default total

runFrom :
     {n      : Nat}
  -> (l      : Parser1 e r s a)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> Either e a

||| Tries to parse a byte vector into a value.
export %inline
run : {n : _} -> Parser1 e r s a -> IBuffer n -> Either e a
run l buf = runFrom l n buf

||| Like `run` but processes a UTF-8 string instead.
export %inline
runString : Parser1 e r s a -> String -> Either e a
runString l s = run l (fromString s)

||| Like `run` but processes a `ByteString` instead.
export
runBytes : Parser1 e r s a -> ByteString -> Either e a
runBytes l (BS s $ BV buf off lte) =
  runFrom l s {x = offsetToIx off} (take (off+s) buf)

||| Like `run` but fails with a proper parse error
||| including error bounds and highlighting of
||| the section where an error occurred.
export %inline
parse :
     {n : _}
  -> Parser1 (BoundedErr e) r s a
  -> Origin
  -> IBuffer n
  -> Either (ParseError e) a
parse l o buf = mapFst (toParseError o (toString buf 0 n)) (run l buf)

||| Like `parse` but processes a UTF-8 string instead.
export %inline
parseString :
     Parser1 (BoundedErr e) r s a
  -> Origin
  -> String
  -> Either (ParseError e) a
parseString l o s = parse l o (fromString s)

||| Like `parse` but processes a `ByteString` instead.
export %inline
parseBytes :
     Parser1 (BoundedErr e) r s a
  -> Origin
  -> ByteString
  -> Either (ParseError e) a
parseBytes l o bs = mapFst (toParseError o (toString bs)) (runBytes l bs)

--------------------------------------------------------------------------------
-- Lexer run loop
--------------------------------------------------------------------------------

parameters {0 s     : Type -> Type}
           {0 r     : Bits32}
           {0 q,e,a : Type}
           {0 n     : Nat}
           (stck    : s q)
           (parser  : P1 q e r s a)
           (buf     : IBuffer n)
           (bytes   : Ref q ByteString)

  step :
       (st          : Index r)
    -> (dfa         : Stepper k q r s)
    -> (cur         : ByteStep k q r s)
    -> (from        : Ix m n)
    -> (pos         : Nat)
    -> {auto x      : Ix pos n}
    -> {auto 0 lte2 : LTE (ixToNat from) (ixToNat x)}
    -> F1 q (Either e a)

  succ :
       (st          : Index r)
    -> (dfa         : Stepper k q r s)
    -> (cur         : ByteStep k q r s)
    -> (last        : Step1 q r s)
    -> (from        : Ix m n)
    -> (pos         : Nat)
    -> {auto x      : Ix pos n}
    -> {auto 0 lte2 : LTE (ixToNat from) (ixToNat x)}
    -> F1 q (Either e a)

  loop : (st : Index r) -> (pos : Nat) -> (x : Ix pos n) => F1 q (Either e a)
  loop st 0     t =
   let _ # t := write1 bytes "" t
    in parser.eoi st stck t
  loop st (S k) t =
   let L _ dfa := parser.lex `at` st
       cur     := dfa `at` 0
    in case cur `atByte` (buf `ix` k) of
         Done f       => let s2 # t := f (stck # t) in loop s2 k t
         Move   nxt f => succ st dfa (dfa `at` nxt) f   x k t
         MoveE  nxt   => step st dfa (dfa `at` nxt)     x k t
         DoneBS f     =>
          let _  # t := writeBS buf x k bytes t
              s2 # t := f (stck # t)
           in loop s2 k t
         _            =>
          let _  # t := writeBS buf x k bytes t
           in fail parser st stck t

  succ st dfa cur f from 0     t =
   let _ # t := writeBS buf from 0 bytes t
    in lastStep parser f st stck t
  succ st dfa cur f from (S k) t =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => succ st dfa cur f from k t
         Done f       => let s2 # t := f (stck # t) in loop s2 k t
         Move   nxt f => succ st dfa (dfa `at` nxt) f from k t
         MoveE  nxt   => step st dfa (dfa `at` nxt)   from k t
         DoneBS f     =>
          let _  # t := writeBS buf from k bytes t
              s2 # t := f (stck # t)
           in loop s2 k t
         Bottom       =>
          let _  # t := writeBS buf from (S k) bytes t
              s2 # t := f (stck # t)
           in loop s2 (S k) t

  step st dfa cur from 0     t =
   let _ # t := writeBS buf from 0 bytes t
    in fail parser st stck t
  step st dfa cur from (S k) t =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep         => step st dfa cur from k t
         Done f       => let s2 # t := f (stck # t) in loop s2 k t
         Move   nxt f => succ st dfa (dfa `at` nxt) f from k t
         MoveE  nxt   => step st dfa (dfa `at` nxt)   from k t
         DoneBS f     =>
          let _  # t := writeBS buf from k bytes t
              s2 # t := f (stck # t)
           in loop s2 k t
         Bottom       =>
          let _  # t := writeBS buf from k bytes t
           in fail parser st stck t

runFrom p pos buf = run1 (go p)
  where
    go : P1 q e r s a -> F1 q (Either e a)
    go p t =
     let x # t := stck p t
      in loop x p buf (bytes @{p.hasb} x) p.init pos t

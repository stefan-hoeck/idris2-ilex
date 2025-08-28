module Text.ILex.Runner

import Data.Buffer
import Text.ILex.Internal.Runner
import public Text.ILex.Parser

%default total

parseFrom :
     {n      : Nat}
  -> (l      : Parser1 e r s a)
  -> (pos    : Nat)
  -> {auto x : Ix pos n}
  -> IBuffer n
  -> Either e a

||| Tries to lex a whole byte vector into a list of bounded
||| tokens.
export %inline
parse : {n : _} -> Parser1 e r s a -> IBuffer n -> Either e a
parse l buf = parseFrom l n buf

||| Like `lex` but processes a UTF-8 string instead.
export %inline
parseString : Parser1 e r s a -> String -> Either e a
parseString l s = parse l (fromString s)

||| Like `lex` but processes a `ByteString` instead.
export
parseBytes : Parser1 e r s a -> ByteString -> Either e a
parseBytes l (BS s $ BV buf off lte) =
  parseFrom l s {x = offsetToIx off} (take (off+s) buf)

--------------------------------------------------------------------------------
-- Lexer run loop
--------------------------------------------------------------------------------

parameters {0 s       : Type -> Type}
           {0 q,e,r,a : Type}
           {0 n       : Nat}
           (stck      : s q)
           (parser    : P1 q e r s a)
           (buf       : IBuffer n)

  succ :
       (st          : r)
    -> (dfa         : Stepper k (Step1 q e r s))
    -> (cur         : ByteStep k (Step1 q e r s))
    -> (last        : Step1 q e r s)
    -> (from        : Ix m n)
    -> (pos         : Nat)
    -> {auto x      : Ix pos n}
    -> {auto 0 lte2 : LTE (ixToNat from) (ixToNat x)}
    -> F1 q (Either e a)

  loop : (st : r) -> (pos : Nat) -> (x : Ix pos n) => F1 q (Either e a)
  loop st 0     t = parser.eoi st stck t
  loop st (S k) t =
   let L _ dfa := dfa1 parser.lex st
       cur     := dfa `at` 0
    in case cur `atByte` (buf `ix` k) of
         Done v      => case v of
           Go  f =>
            let s2 # t := f (stck # t)
             in loop s2 k t
           Rd  f =>
            let s2 # t := f (B stck (toBS buf x k) t)
             in loop s2 k t
           Prs f => case f (B stck (toBS buf x k) t) of
             Right s2 # t => loop s2 k t
             Left  x  # t => Left x # t
           Err => fail parser st stck (toBS buf x k) t
         Move nxt f => succ st dfa (dfa `at` nxt) f   x k t
         Keep       => succ st dfa cur            Err x k t
         Bottom     => fail parser st stck (toBS buf x k) t

  succ st dfa cur v from 0     t =
    lastStep parser v st stck (toBS buf from 0) t
  succ st dfa cur v from (S k) t =
   let byte := buf `ix` k
    in case cur `atByte` byte of
         Keep       => succ st dfa cur v from k t
         Done v     => case v of
           Go  f =>
            let s2 # t := f (stck # t)
             in loop s2 k t
           Rd  f =>
            let s2 # t := f (B stck (toBS buf from k) t)
             in loop s2 k t
           Prs f => case f (B stck (toBS buf from k) t) of
             Right s2 # t => loop s2 k t
             Left  x  # t => Left x # t
           Err => fail parser st stck (toBS buf from k) t
         Move nxt f => succ st dfa (dfa `at` nxt) f from k t
         Bottom     => case v of
           Go  f =>
            let s2 # t := f (stck # t)
             in loop s2 (S k) t
           Rd  f =>
            let s2 # t := f (B stck (toBS buf from (S k)) t)
             in loop s2 (S k) t
           Prs f => case f (B stck (toBS buf from (S k)) t) of
             Right s2 # t => loop s2 (S k) t
             Left  x  # t => Left x # t
           Err => fail parser st stck (toBS buf from k) t

parseFrom p pos buf = run1 (go p)
  where
    go : P1 q e r s a -> F1 q (Either e a)
    go p t =
      let x # t := stck p t
       in loop x p buf p.init pos t

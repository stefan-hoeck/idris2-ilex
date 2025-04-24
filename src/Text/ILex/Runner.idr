module Text.ILex.Runner

import Data.Array.Core
import Data.Array.Indexed
import Data.Buffer
import Data.Buffer.Core
import Data.Buffer.Indexed
import Data.Vect
import Derive.Prelude

%default total
%language ElabReflection

public export
data Info : Type -> Type where
  Err    : Info a
  Ignore : Info a
  Final  : (val : a) -> Info a

parameters {0 a    : Type}
           {states : Nat}
           (next   : IArray (S states) (IArray 256 (Fin (S states))))
           (term   : IArray (S states) (Info a))


  loop :
       (vals   : SnocList a)
    -> (buf    : IBuffer n)
    -> (pos    : Nat)
    -> {auto x : Ix pos n}
    -> (cur    : Fin (S states))
    -> Either (Nat,Bits8) (List a)
  loop vals buf 0     cur =
    case term `at` cur of
      Err       => Left  (ixToNat x, 0)
      Ignore    => Right (vals <>> [])
      Final val => Right (vals <>> [val])
  loop vals buf (S k) cur =
    let arr  := next `at` cur
        byte := ix buf k
     in case arr `atByte` byte of
          FZ => case term `at` cur of
            Err       => Left (ixToNat x, buf `ix` k)
            Ignore    => loop vals buf k (atByte (at next FZ) byte)
            Final val => loop (vals :< val) buf k (atByte (at next FZ) byte)
          x  => loop vals buf k x

  export
  lex : (n ** IBuffer n) -> Either (Nat,Bits8) (List a)
  lex (n ** buf) = loop [<] buf n 0

  export
  lexString : String -> Either (Nat,Bits8) (List a)
  lexString s = lex (_ ** fromString s)

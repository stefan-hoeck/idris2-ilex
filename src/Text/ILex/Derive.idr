module Text.ILex.Derive

import public Language.Reflection
import public Language.Reflection.Syntax

%default total


export
deriveParserState :
     {auto elb : Elaboration m}
  -> (size, state : Name)
  -> (states : List Name)
  -> m ()
deriveParserState sz st ss =
 let count      := primVal $ B32 $ cast (length ss)
     decls      := go [<] count ss 0
     sizeClaim  := public' sz `(Bits32)
     sizeDefn   := def sz [patClause (var sz) count]
     stateClaim := claim M0 Public [] st type
     stateDefn  := def st [patClause (var st) `(Index ~(var sz))]

  in declare (sizeClaim :: sizeDefn :: stateClaim :: stateDefn :: decls)

  where
    go : SnocList Decl -> TTImp -> List Name -> Bits32 -> List Decl
    go sd c []      _ = sd <>> []
    go sd c (n::ns) x =
     let nvar  := var n
         claim := export' n `(Index ~(c))
         defn  := def n [patClause nvar `(I ~(primVal $ B32 x))]
      in go (sd :< claim :< defn) c ns (x+1)

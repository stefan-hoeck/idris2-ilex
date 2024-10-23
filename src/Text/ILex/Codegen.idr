module Text.ILex.Codegen

import Data.String
import Language.Reflection.Util
import Text.ILex.DFA

%default total

vright : Value
vright = VPlain "Right"

vleft : Value
vleft  = VPlain "Left"

vstr : Value
vstr = VPlain "str"

vcs : Value
vcs = VPlain "cs"

vc : Value
vc = VPlain "c"

vnil : Value
vnil = VPlain "Nil"

varg : Nat -> Value
varg n = VPlain "x\{show n}"

applyArgs : UArgs -> Nat -> Value -> Value
applyArgs [<]       k v = v
applyArgs (sx :< x) k v = VApp (applyArgs sx (S k) v) (varg k)

applyConvs : UConversions -> Value -> Value
applyConvs [<]       v = v
applyConvs (sc :< c) v = VApp (applyConvs sc v) (convToVal c)

applyConv : Conv -> UArgs -> Value -> Value
applyConv ID      args v = applyArgs args 0 v
applyConv (UC cs) args v = applyConvs cs v
applyConv (EC cs) args v = applyConvs cs vleft

result : UArgs -> Conv -> Value
result args ID      = applyArgs args 0 vright
result args (UC cs) = applyConvs cs vright
result args (EC cs) = applyConvs cs vleft

subName : String -> Bits32 -> Value
subName s m = VPlain "\{s}\{show m}"

pat : Rule -> String
pat (P p) = interpolate (VApp p.val vc)
pat _     = "c /= '\\n'"

unexpected : Value
unexpected =
  VApp vleft (VApp (VPlain "cast") (VApp (VPlain "Unexpected") vc))

eoi : Value
eoi = VApp vleft (VApp (VPlain "cast") (VPlain "EOI"))

parameters (args : UArgs)
           (nm   : String)

  export
  invoke : Bits32 -> Conv -> Value -> Value
  invoke 0 c cs = result args c
  invoke n c cs = applyConv c args (VApp (subName nm n) cs)

  charCls : Bits32 -> Char -> Conv -> String
  charCls k ch c = "    \{show ch} => \{invoke k c vcs}"

  remClause1 : Nat -> Value -> Deltas -> List String
  remClause1 i cl []             = [indent i "_   => \{cl}"]
  remClause1 i cl [D A c t]      = [indent i "_   => \{invoke t c vcs}"]
  remClause1 i cl (D r c t ::ds) =
    indent i     "_  => case \{pat r} of" ::
    indent (i+2) "True => \{invoke t c vcs}" ::
    remClause1 (i+2) cl ds

  remClause : Nat -> Value -> Deltas -> List String
  remClause i cl [D r c t] =
    [ indent i     "case \{pat r} of"
    , indent (i+2) "True => \{invoke t c vcs}"
    , indent (i+2) "_    => \{cl}"
    ]
  remClause i cl (D r c t::ds) =
    indent i     "case \{pat r} of" ::
    indent (i+2) "True => \{invoke t c vcs}" ::
    indent (i+2) "_    =>" ::
    remClause (i+4) cl ds
  remClause i cl [] = []

  charClauses : Value -> Deltas -> List String
  charClauses dflt (D (C ch) c t::ds) = charCls t ch c :: charClauses dflt ds
  charClauses dflt ds                 = remClause1 4 dflt ds

  charClause : Value -> Deltas -> List String
  charClause dflt ds = "  case c of" :: charClauses dflt ds

  catchAll : Deltas -> Value
  catchAll (D Eps _ _ :: D A c t :: _) = invoke t c vstr
  catchAll (D Eps c t :: _)            = invoke t c vstr
  catchAll (D A c t :: _)              = invoke t c vstr
  catchAll _                           = unexpected

  consCase : Deltas -> Value -> List String
  consCase ds v =
    case ds of
      D (C _) _ _::_  => charClause v ds
      _               => remClause 2 v ds

  nilCase : Deltas -> Value
  nilCase (D Eps c t :: _) = invoke t c vnil
  nilCase _                = eoi

lexType : (res : Tpe) -> UArgs -> Tpe
lexType res args = piAll res (tpeof (List Char) :: (args <>> []))

decl : String -> (res : Tpe) -> (Bits32,Node) -> String
decl n res (x,N args ds) =
  "\npublic export\n\{subName n x} : \{lexType res args}"

rem : Deltas -> Deltas
rem (D Eps _ _ :: ds) = rem ds
rem (D A   _ _ :: ds) = rem ds
rem ds                = ds

defn : String -> (Bits32,Node) -> String
defn s (x,N args [D Eps c t]) =
 let name := subName s x
     lhs  := applyArgs args 0 (VApp name vstr)
     rhs  := invoke args s t c vstr
  in "\n\{lhs} = \{rhs}"
defn s (x,N args ds) =
 let name := subName s x
     consLHS := applyArgs args 0 (VApp name $ VPlain "str@(c::cs)")
     nilLHS  := applyArgs args 0 (VApp name $ VPlain "[]")
  in case rem ds of
       []  =>
         fastUnlines $
           "\{consLHS} = \{catchAll args s ds}" ::
           ["\{nilLHS} = \{nilCase args s ds}"]
       rem =>
         fastUnlines $
           "\{consLHS} =" :: consCase args s rem (catchAll args s ds) ++
           ["\{nilLHS} = \{nilCase args s ds}"]

export covering
generate :
     {auto c  : Cast LexErr e}
  -> {auto te : ToType e}
  -> {auto ta : ToType a}
  -> String
  -> Expr b e [<] [<a]
  -> String
generate n r =
 let g      := toDFA (toType a) r
     resTpe := tpeof (Either e a)
  in fastUnlines $
       ("\npublic export\n\{n} : String -> \{resTpe}" ::
       map (decl n resTpe) g) ++
       ("\n\{n} = \{subName n 1} . unpack" :: map (defn n) g)

-- covering
-- main : IO ()
-- main = do
--   putStrLn
--     """
--     module Lex.Lexers
--
--     import Lex.Util
--
--     %default total
--     """
--   putStrLn (compile "lexNat" lexErrTpe (mtlift Integer) natural)

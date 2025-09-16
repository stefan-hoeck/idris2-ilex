module Text.ILex.Derive

import public Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
-- Deriving Parser States
--------------------------------------------------------------------------------

||| Given names for the number of states (`size`), the
||| parser state (`state`), and the distinct parser states,
||| this will compute the actual number of states and define
||| a constant for each state.
|||
||| For instance, `deriveParserState "SZ" "ST" ["SIni", "Str", "Err", "Done"]`
||| will generate the following definitions:
|||
||| ```idris
||| public export
||| SZ : Bits32
||| SZ = 4
|||
||| public export
||| 0 ST : Type
||| ST = Index SZ
|||
||| export
||| SIni : ST
||| SIni = I 0
|||
||| export
||| Str : ST
||| Str = I 1
|||
||| export
||| Err : ST
||| Err = I 2
|||
||| export
||| Done : ST
||| Done = I 3
|||
||| export
||| showST : ST -> String
||| showST (I 0) = "SIni"
||| showST (I 1) = "Str"
||| showST (I 2) = "Err"
||| showST (I 3) = "Done"
||| showST _     = "impossible"
||| ```
export
deriveParserState :
     {auto elb : Elaboration m}
  -> (size, state : Name)
  -> (states : List Name)
  -> m ()
deriveParserState sz st ss =
 let count      := primVal $ B32 $ cast (length ss)
     decls      := defs [<] count ss 0
     sizeClaim  := public' sz `(Bits32)
     sizeDefn   := def sz [patClause (var sz) count]
     stateClaim := claim M0 Public [] st type
     stateDefn  := def st [patClause (var st) `(Index ~(var sz))]
     showName   := fromString "show\{st}"
     showVar    := var showName
     showClaim  := export' showName `(~(var st) -> String)
     showDecl   := def showName (shows [<] showVar ss 0)

  in declare $
       [sizeClaim, sizeDefn, stateClaim, stateDefn] ++ decls ++ [showClaim, showDecl]

  where
    defs : SnocList Decl -> TTImp -> List Name -> Bits32 -> List Decl
    defs sd c []      _ = sd <>> []
    defs sd c (n::ns) x =
     let claim := export' n (var st)
         defn  := def n [patClause (var n) `(I ~(primVal $ B32 x))]
      in defs (sd :< claim :< defn) c ns (x+1)

    shows : SnocList Clause -> TTImp -> List Name -> Bits32 -> List Clause
    shows sc v []      _ = sc <>> [patClause `(~(v) _) `("impossible")]
    shows sc v (n::ns) x =
     let c := patClause `(~(v) (I ~(primVal $ B32 x))) n.namePrim
      in shows (sc :< c) v ns (x+1)

--------------------------------------------------------------------------------
-- Deriving Interfaces
--------------------------------------------------------------------------------

dropLastArg : List Arg -> List Arg
dropLastArg args =
  case [<] <>< args of
    sa :< _ => sa <>> []
    [<]     => []

unapply1 : TTImp -> TTImp
unapply1 (IApp      fc f _)   = f
unapply1 (INamedApp fc f _ _) = f
unapply1 t                    = t

ifaceType : ParamTypeInfo -> TTImp -> TTImp
ifaceType p t = piAll t (dropLastArg p.implicits)

||| Derives an implementation of `HasPosition` for a record type with the
||| following fields:
|||
||| ```idris
||| line_      : Ref q Nat
||| col_       : Ref q Nat
||| positions_ : Ref q Nat
||| ```
export
HasPosition : List Name -> ParamTypeInfo -> Res (List TopLevel)
HasPosition nms p =
 let impl := implName p "HasPosition"
  in Right [ TL (clm impl) (dfn impl) ]
  where
    clm : (impl : Name) -> Decl
    clm impl =
     let arg := unapply1 p.applied
      in implClaimVis Export impl (ifaceType p $ var "HasPosition" `app` arg)

    dfn : (impl : Name) -> Decl
    dfn impl = def impl [patClause (var impl) `(MkHP line_ col_ positions_)]

||| Derives an implementation of `HasBytes` for a record type with the
||| following field:
|||
||| ```idris
||| bytes_     : Ref q ByteString
||| ```
export
HasBytes : List Name -> ParamTypeInfo -> Res (List TopLevel)
HasBytes nms p =
 let impl := implName p "HasBytes"
  in Right [ TL (clm impl) (dfn impl) ]
  where
    clm : (impl : Name) -> Decl
    clm impl =
     let arg := unapply1 p.applied
      in implClaimVis Export impl (ifaceType p $ var "HasBytes" `app` arg)

    dfn : (impl : Name) -> Decl
    dfn impl = def impl [patClause (var impl) `(MkHB bytes_)]

||| Derives an implementation of `HasStringLits` for a record type with the
||| following field:
|||
||| ```idris
||| strings_     : Ref q (SnocList String)
||| ```
export
HasStringLits : List Name -> ParamTypeInfo -> Res (List TopLevel)
HasStringLits nms p =
 let impl := implName p "HasStringLits"
  in Right [ TL (clm impl) (dfn impl) ]
  where
    clm : (impl : Name) -> Decl
    clm impl =
     let arg := unapply1 p.applied
      in implClaimVis Export impl (ifaceType p $ var "HasStringLits" `app` arg)

    dfn : (impl : Name) -> Decl
    dfn impl = def impl [patClause (var impl) `(MkHSL strings_)]

errErr : Res a
errErr = Left "HasError can only be derived for a record type with a field name `error_`"

errType : ParamTypeInfo -> Res TTImp
errType p =
  case p.cons of
    [c] => go (toList c.args)
    _   => errErr
  where
    go : List (ConArg p.numParams) -> Res TTImp
    go []      = errErr
    go (ParamArg {}::as) = go as
    go (CArg mnm rig pinfo x::as) =
      case mnm == Just "error_" of
        False => go as
        True  => case x of
          -- `Ref q (Maybe (BoundedErr e))`
          (PApp refq (PApp m (PApp b z))) => Right (ttimp p.paramNames z)
          _                               => errErr

||| Derives an implementation of `HasError` for a record type with the
||| following field:
|||
||| ```idris
||| error_     : Ref q (Maybe $ BoundedErr e)
||| ```
|||
||| The error type `e` can be freely chosen (it can also be a parameter) and
||| will be determined when deriving the implementation.
export
HasError : List Name -> ParamTypeInfo -> Res (List TopLevel)
HasError nms p =
 let impl := implName p "HasError"
     Right c := clm impl | Left x => Left x
  in Right [TL c (dfn impl)]
  where
    clm : (impl : Name) -> Res Decl
    clm impl =
     let arg      := unapply1 p.applied
         Right te := errType p | Left x => Left x
      in Right $ implClaimVis Export impl (ifaceType p $ appAll "HasError" [arg,te])

    dfn : (impl : Name) -> Decl
    dfn impl = def impl [patClause (var impl) `(MkHE error_)]

stackErr : Res a
stackErr = Left "HasStack can only be derived for a record type with a field name `stack_`"

stackType : ParamTypeInfo -> Res TTImp
stackType p =
  case p.cons of
    [c] => go (toList c.args)
    _   => stackErr
  where
    go : List (ConArg p.numParams) -> Res TTImp
    go []      = stackErr
    go (ParamArg {}::as) = go as
    go (CArg mnm rig pinfo x::as) =
      case mnm == Just "stack_" of
        False => go as
        True  => case x of
          -- `Ref q a`
          (PApp refq z) => Right (ttimp p.paramNames z)
          _             => stackErr

||| Derives an implementation of `HasStack` for a record type with the
||| following field:
|||
||| ```idris
||| stack_     : Ref q a
||| ```
|||
||| The stack type `a` can be freely chosen (it can also be a parameter) and
||| will be determined when deriving the implementation.
export
HasStack : List Name -> ParamTypeInfo -> Res (List TopLevel)
HasStack nms p =
 let impl := implName p "HasStack"
     Right c := clm impl | Left x => Left x
  in Right [TL c (dfn impl)]
  where
    clm : (impl : Name) -> Res Decl
    clm impl =
     let arg      := unapply1 p.applied
         Right ts := stackType p | Left x => Left x
      in Right $ implClaimVis Export impl (ifaceType p $ appAll "HasStack" [arg,ts])

    dfn : (impl : Name) -> Decl
    dfn impl = def impl [patClause (var impl) `(MkHS stack_)]

||| Derives implementations of the following interfaces for a suitable
||| record type: `HasPosition`, `HasBytes`, `HasStringLits`, `HasError`, and
||| `HasStack`.
export
FullStack : List Name -> ParamTypeInfo -> Res (List TopLevel)
FullStack nms p =
  sequenceJoin
    [ HasPosition nms p
    , HasBytes nms p
    , HasStringLits nms p
    , HasError nms p
    , HasStack nms p
    ]

module Derive.FromDouble

import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
fromDblClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
fromDblClaim vis fun p =
  let arg := p.applied
      tpe := piAll `(Double -> ~(arg)) (allImplicits p "FromDouble")
   in simpleClaim vis fun tpe

||| Top-level declaration implementing the `Eq` interface for
||| the given data type.
export
dblImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
dblImplClaim v impl p = implClaimVis v impl (implType "FromDouble" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

dblImplDef : (fd, impl : Name) -> Decl
dblImplDef fd impl =
  def impl [patClause (var impl) (appNames "MkFromDouble" [fd])]

export
fromDblDef : Name -> Con n vs -> Decl
fromDblDef f c =
  let t := `(fromDouble n)
   in def f [patClause (var f `app` bindVar "n") (injArgs explicit (const t) c)]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `FromDouble` for a
||| single-constructor data type.
export
FromDoubleVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
FromDoubleVis vis nms p = case p.info.cons of
  [c] =>
    let fun  := funName p "fromDouble"
        impl := implName p "FromDouble"
     in Right [ TL (fromDblClaim vis fun p) (fromDblDef fun c)
              , TL (dblImplClaim vis impl p) (dblImplDef fun impl)
              ]
  _   => failRecord "FromDouble"

||| Alias for `FromDoubleVis Public`
export %inline
FromDouble : List Name -> ParamTypeInfo -> Res (List TopLevel)
FromDouble = FromDoubleVis Public

module Derive.FromDouble

import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
fromDblClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
fromDblClaim fun p =
  let arg := p.applied
      tpe := piAll `(Double -> ~(arg)) (allImplicits p "FromDouble")
   in public' fun tpe

||| Top-level declaration implementing the `Eq` interface for
||| the given data type.
export
dblImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
dblImplClaim impl p = implClaim impl (implType "FromDouble" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

dblImplDef : (fd, impl : Name) -> Decl
dblImplDef fd impl = def impl [var impl .= appNames "MkFromDouble" [fd]]

export
fromDblDef : Name -> Con n vs -> Decl
fromDblDef f c =
  let t := `(fromDouble n)
   in def f [var f .$ bindVar "n" .= injArgs explicit (const t) c]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `FromDouble` for a
||| single-constructor data type.
export
FromDouble : List Name -> ParamTypeInfo -> Res (List TopLevel)
FromDouble nms p = case p.info.cons of
  [c] =>
    let fun  := funName p "fromDouble"
        impl := implName p "FromDouble"
     in Right [ TL (fromDblClaim fun p) (fromDblDef fun c)
              , TL (dblImplClaim impl p) (dblImplDef fun impl)
              ]
  _   => failRecord "FromDouble"

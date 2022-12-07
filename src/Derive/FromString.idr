module Derive.FromString

import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
fromStrClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
fromStrClaim fun p =
  let arg := p.applied
      tpe := piAll `(String -> ~(arg)) (allImplicits p "FromString")
   in public' fun tpe

||| Top-level declaration implementing the `FromString` interface for
||| the given data type.
export
strImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
strImplClaim impl p = implClaim impl (implType "FromString" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

strImplDef : (fd, impl : Name) -> Decl
strImplDef fd impl = def impl [var impl .= appNames "MkFromString" [fd]]

export
fromStrDef : Name -> Con n vs -> Decl
fromStrDef f c =
  let t := `(fromString n)
   in def f [var f .$ bindVar "n" .= injArgs explicit (const t) c]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `FromString` for a
||| single-constructor data type.
|||
||| All fields of the data type will be filled with the result of a call to
||| `fromString s`, where `s` is the string to be used. This makes mostly
||| sense for newtypes, but is supported for any single-constructor data type
||| to be consistent with restrictions on `Num` and `FromDouble`.
export
FromString : List Name -> ParamTypeInfo -> Res (List TopLevel)
FromString nms p = case p.info.cons of
  [c] =>
    let fun  := funName p "fromString"
        impl := implName p "FromString"
     in Right [ TL (fromStrClaim fun p) (fromStrDef fun c)
              , TL (strImplClaim impl p) (strImplDef fun impl)
              ]
  _   => failRecord "FromString"

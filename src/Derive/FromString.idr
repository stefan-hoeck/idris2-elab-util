module Derive.FromString

import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
fromStrClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
fromStrClaim vis fun p =
  let arg := p.applied
      tpe := piAll `(String -> ~(arg)) (allImplicits p "FromString")
   in simpleClaim vis fun tpe

||| Top-level declaration implementing the `FromString` interface for
||| the given data type.
export
strImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
strImplClaim v impl p = implClaimVis v impl (implType "FromString" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

strImplDef : (fd, impl : Name) -> Decl
strImplDef fd impl =
  def impl [patClause (var impl) (appNames "MkFromString" [fd])]

export
fromStrDef : Name -> Con n vs -> Decl
fromStrDef f c =
  let t := `(fromString n)
   in def f [patClause (var f `app` bindVar "n") (injArgs explicit (const t) c)]

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
FromStringVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
FromStringVis vis nms p = case p.info.cons of
  [c] =>
    let fun  := funName p "fromString"
        impl := implName p "FromString"
     in Right
          [ TL (fromStrClaim vis fun p) (fromStrDef fun c)
          , TL (strImplClaim vis impl p) (strImplDef fun impl)
          ]
  _   => failRecord "FromString"

||| Alias for `FromStringVis Public`
export %inline
FromString : List Name -> ParamTypeInfo -> Res (List TopLevel)
FromString = FromStringVis Public

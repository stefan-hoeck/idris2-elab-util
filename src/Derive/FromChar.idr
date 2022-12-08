module Derive.FromChar

import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
fromChrClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
fromChrClaim vis fun p =
  let arg := p.applied
      tpe := piAll `(Char -> ~(arg)) (allImplicits p "FromChar")
   in simpleClaim vis fun tpe

||| Top-level declaration implementing the `FromChar` interface for
||| the given data type.
export
chrImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
chrImplClaim v impl p = implClaimVis v impl (implType "FromChar" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

chrImplDef : (fd, impl : Name) -> Decl
chrImplDef fd impl = def impl [var impl .= appNames "MkFromChar" [fd]]

export
fromChrDef : Name -> Con n vs -> Decl
fromChrDef f c =
  let t := `(fromChar n)
   in def f [var f .$ bindVar "n" .= injArgs explicit (const t) c]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `FromChar` for a
||| single-constructor data type.
|||
||| All fields of the data type will be filled with the result of a call to
||| `fromChar s`, where `s` is the string to be used. This makes mostly
||| sense for newtypes, but is supported for any single-constructor data type
||| to be consistent with restrictions on `Num` and `FromDouble`.
export
FromCharVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
FromCharVis vis nms p = case p.info.cons of
  [c] =>
    let fun  := funName p "fromChar"
        impl := implName p "FromChar"
     in Right [ TL (fromChrClaim vis fun p) (fromChrDef fun c)
              , TL (chrImplClaim vis impl p) (chrImplDef fun impl)
              ]
  _   => failRecord "FromChar"

||| Alias for `FromCharVis Public`
export %inline
FromChar : List Name -> ParamTypeInfo -> Res (List TopLevel)
FromChar = FromCharVis Public

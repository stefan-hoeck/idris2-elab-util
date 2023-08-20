module Derive.Abs

import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
absClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
absClaim vis fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg)) (allImplicits p "Abs")
   in simpleClaim vis fun tpe

export
absImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
absImplClaim vis impl p = implClaimVis vis impl (implType "Abs" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

absImplDef : (abs, impl : Name) -> Decl
absImplDef abs impl = def impl [patClause (var impl) (appNames "MkAbs" [abs])]

parameters (nms : List Name)
  abs : BoundArg 1 Explicit -> TTImp
  abs (BA _ [x] _)  = `(abs ~(varStr x))

  export
  absDef : Name -> Con n vs -> Decl
  absDef fun c = def fun [mapArgs explicit (var fun `app`) abs c]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Abs` for a
||| single-constructor data type with the given visibility.
export
AbsVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
AbsVis vis nms p = case p.info.cons of
  [c] =>
    let abs  := funName p "abs"
        impl := implName p "Abs"
     in Right
          [ TL (absClaim vis abs p) (absDef nms abs c)
          , TL (absImplClaim vis impl p) (absImplDef abs impl)
          ]
  _   => failRecord "Abs"

||| Generate declarations and implementations for `Abs` for a
||| single-constructor data type with `public export` visibility.
export %inline
Abs : List Name -> ParamTypeInfo -> Res (List TopLevel)
Abs = AbsVis Public

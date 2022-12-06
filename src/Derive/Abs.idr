module Derive.Abs

import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
absClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
absClaim fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg)) (allImplicits p "Abs")
   in public' fun tpe

export
absImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
absImplClaim impl p = implClaim impl (implType "Abs" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

absImplDef : (abs, impl : Name) -> Decl
absImplDef abs impl = def impl [var impl .= appNames "MkAbs" [abs]]

parameters (nms : List Name)
  abs : BoundArg 1 Explicit -> TTImp
  abs (BA _ [x] _)  = `(abs ~(varStr x))

  export
  absDef : Name -> Con n vs -> Decl
  absDef fun c = def fun [mapArgs explicit (var fun .$) abs c]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Abs` for a
||| single-constructor data type.
export
Abs : List Name -> ParamTypeInfo -> Res (List TopLevel)
Abs nms p = case p.info.cons of
  [c] =>
    let abs     := funName p "abs"
        impl    := implName p "Abs"
     in Right [ TL (absClaim abs p) (absDef nms abs c)
              , TL (absImplClaim impl p) (absImplDef abs impl)
              ]
  _   => failRecord "Abs"

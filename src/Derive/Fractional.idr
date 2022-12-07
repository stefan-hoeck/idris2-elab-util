module Derive.Fractional

import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
divClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
divClaim fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg) -> ~(arg)) (allImplicits p "Fractional")
   in public' fun tpe

export
recipClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
recipClaim fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg)) (allImplicits p "Fractional")
   in public' fun tpe

export
fractionalImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
fractionalImplClaim i p = implClaim i (implType "Fractional" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

fractionalImplDef : (div, recip, impl : Name) -> Decl
fractionalImplDef d r i = def i [var i .= appNames "MkFractional" [d, r]]

div : BoundArg 2 Explicit -> TTImp
div (BA arg [x,y] _)  = `(~(varStr x) / ~(varStr y))

recip : BoundArg 1 Explicit -> TTImp
recip (BA arg [x] _)  = `(recip ~(varStr x))

export
divDef : Name -> Con n vs -> Decl
divDef fun c =
  let clause := mapArgs2 explicit (\x,y => var fun .$ x .$ y) div c
   in def fun [clause]

export
recipDef : Name -> Con n vs -> Decl
recipDef fun c =
  let clause := mapArgs explicit (var fun .$) recip c
   in def fun [clause]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Fractional` for a
||| single-constructor data type.
export
Fractional : List Name -> ParamTypeInfo -> Res (List TopLevel)
Fractional nms p = case p.info.cons of
  [c] =>
    let recip := funName p "recip"
        div   := funName p "divide"
        impl  := implName p "Fractional"
     in Right [ TL (recipClaim recip p) (recipDef recip c)
              , TL (divClaim div p) (divDef div c)
              , TL (fractionalImplClaim impl p) (fractionalImplDef div recip impl)
              ]
  _   => failRecord "Fractional"

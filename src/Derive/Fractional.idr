module Derive.Fractional

import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
divClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
divClaim vis fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg) -> ~(arg)) (allImplicits p "Fractional")
   in simpleClaim vis fun tpe

export
recipClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
recipClaim vis fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg)) (allImplicits p "Fractional")
   in simpleClaim vis fun tpe

export
fractionalImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
fractionalImplClaim v i p = implClaimVis v i (implType "Fractional" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

fractionalImplDef : (div, recip, impl : Name) -> Decl
fractionalImplDef d r i =
  def i [patClause (var i) (appNames "MkFractional" [d, r])]

div : BoundArg 2 Explicit -> TTImp
div (BA arg [x,y] _)  = `(~(varStr x) / ~(varStr y))

recip : BoundArg 1 Explicit -> TTImp
recip (BA arg [x] _)  = `(recip ~(varStr x))

export
divDef : Name -> Con n vs -> Decl
divDef fun c =
  let clause := mapArgs2 explicit (\x,y => `(~(var fun) ~(x) ~(y))) div c
   in def fun [clause]

export
recipDef : Name -> Con n vs -> Decl
recipDef fun c =
  let clause := mapArgs explicit (var fun `app`) recip c
   in def fun [clause]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Fractional` for a
||| single-constructor data type.
export
FractionalVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
FractionalVis vis nms p = case p.info.cons of
  [c] =>
    let recip := funName p "recip"
        div   := funName p "divide"
        impl  := implName p "Fractional"
     in Right [ TL (recipClaim vis recip p) (recipDef recip c)
              , TL (divClaim vis div p) (divDef div c)
              , TL (fractionalImplClaim vis impl p) (fractionalImplDef div recip impl)
              ]
  _   => failRecord "Fractional"

||| Alias for `FractionalVis Public`
export %inline
Fractional : List Name -> ParamTypeInfo -> Res (List TopLevel)
Fractional = FractionalVis Public

module Derive.Integral

import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
dvClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
dvClaim vis fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg) -> ~(arg)) (allImplicits p "Integral")
   in simpleClaim vis fun tpe

export
intImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
intImplClaim v impl p = implClaimVis v impl (implType "Integral" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

intImplDef : (div, mod, impl : Name) -> Decl
intImplDef d m impl =
  def impl [patClause (var impl) (appNames "MkIntegral" [d,m])]

parameters (nms : List Name)
  div : BoundArg 2 Explicit -> TTImp
  div (BA arg [x,y] _)  = `(div ~(varStr x) ~(varStr y))

  mod : BoundArg 2 Explicit -> TTImp
  mod (BA arg [x,y] _)  = `(mod ~(varStr x) ~(varStr y))

  export
  divDef : Name -> Con n vs -> Decl
  divDef fun c =
    let clause := mapArgs2 explicit (\x,y => `(~(var fun) ~(x) ~(y))) div c
     in def fun [clause]

  export
  modDef : Name -> Con n vs -> Decl
  modDef fun c =
    let clause := mapArgs2 explicit (\x,y => `(~(var fun) ~(x) ~(y))) mod c
     in def fun [clause]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Integral` for a
||| single-constructor data type.
export
IntegralVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
IntegralVis vis nms p = case p.info.cons of
  [c] =>
    let div  := funName p "div"
        mod  := funName p "mod"
        impl := implName p "Integral"
     in Right [ TL (dvClaim vis div p) (divDef nms div c)
              , TL (dvClaim vis mod p) (modDef nms mod c)
              , TL (intImplClaim vis impl p) (intImplDef div mod impl)
              ]
  _   => failRecord "Integral"

||| Alias for `IntegralVis Public`
export %inline
Integral : List Name -> ParamTypeInfo -> Res (List TopLevel)
Integral = IntegralVis Public

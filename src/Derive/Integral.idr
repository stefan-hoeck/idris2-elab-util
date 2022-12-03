module Derive.Integral

import Derive.Record
import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
dvClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
dvClaim fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg) -> ~(arg)) (allImplicits p "Integral")
   in public' fun tpe

export
intImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
intImplClaim impl p = implClaim impl (implType "Integral" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

intImplDef : (div, mod, impl : Name) -> Decl
intImplDef d m impl = def impl [var impl .= appNames "MkIntegral" [d,m]]

parameters (nms : List Name)
  div : BoundArg 2 Explicit -> TTImp
  div (BA arg [x,y] _)  = `(div ~(x) ~(y))

  mod : BoundArg 2 Explicit -> TTImp
  mod (BA arg [x,y] _)  = `(mod ~(x) ~(y))

  export
  divDef : Name -> Con n vs -> Decl
  divDef fun c =
    let clause := mapArgs2 explicit (\x,y => var fun .$ x .$ y) div c
     in def fun [clause]

  export
  modDef : Name -> Con n vs -> Decl
  modDef fun c =
    let clause := mapArgs2 explicit (\x,y => var fun .$ x .$ y) mod c
     in def fun [clause]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Integral` for a
||| single-constructor data type.
export
Integral : List Name -> ParamRecord -> List TopLevel
Integral nms (Element p _) =
  let div  := funName p "div"
      mod  := funName p "mod"
      impl := implName p "Integral"
      con  := getConstructor p.info
   in [ TL (dvClaim div p) (divDef nms div con)
      , TL (dvClaim mod p) (modDef nms mod con)
      , TL (intImplClaim impl p) (intImplDef div mod impl)
      ]

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
  div (BA arg [x,y] _)  = `(div ~(var x) ~(var y))

  mod : BoundArg 2 Explicit -> TTImp
  mod (BA arg [x,y] _)  = `(mod ~(var x) ~(var y))

  export
  divClause :
       (fun        : Name)
    -> (t          : TypeInfo)
    -> {auto 0 prf : Record t}
    -> Clause
  divClause fun (MkTypeInfo n k as [c]) {prf = IsRecord} =
    let nx := freshNames "x" c.arty
        ny := freshNames "y" c.arty
        st := div <$> boundArgs explicit c.args [nx,ny]
     in var fun .$ bindCon c nx .$ bindCon c ny .= appAll c.name (st <>> [])

  -- TODO: Less copy-paste
  export
  modClause :
       (fun        : Name)
    -> (t          : TypeInfo)
    -> {auto 0 prf : Record t}
    -> Clause
  modClause fun (MkTypeInfo n k as [c]) {prf = IsRecord} =
    let nx := freshNames "x" c.arty
        ny := freshNames "y" c.arty
        st := mod <$> boundArgs explicit c.args [nx,ny]
     in var fun .$ bindCon c nx .$ bindCon c ny .= appAll c.name (st <>> [])

  export
  divDef : Name -> (t : TypeInfo) -> {auto 0 _ : Record t} -> Decl
  divDef fun ti = def fun [divClause fun ti]

  export
  modDef : Name -> (t : TypeInfo) -> {auto 0 _ : Record t} -> Decl
  modDef fun ti = def fun [modClause fun ti]

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
   in [ TL (dvClaim div p) (divDef nms div p.info)
      , TL (dvClaim mod p) (modDef nms mod p.info)
      , TL (intImplClaim impl p) (intImplDef div mod impl)
      ]

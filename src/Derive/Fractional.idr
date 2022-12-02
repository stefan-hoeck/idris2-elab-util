module Derive.Fractional

import Derive.Record
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

parameters (nms : List Name)
  div : BoundArg 2 Explicit -> TTImp
  div (BA arg [x,y] _)  = `(~(var x) / ~(var y))

  recip : BoundArg 1 Explicit -> TTImp
  recip (BA arg [x] _)  = `(recip ~(var x))

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
  recipClause :
       (fun        : Name)
    -> (t          : TypeInfo)
    -> {auto 0 prf : Record t}
    -> Clause
  recipClause fun (MkTypeInfo n k as [c]) {prf = IsRecord} =
    let nx := freshNames "x" c.arty
        st := recip <$> boundArgs explicit c.args [nx]
     in var fun .$ bindCon c nx .= appAll c.name (st <>> [])

  export
  divDef : Name -> (t : TypeInfo) -> {auto 0 _ : Record t} -> Decl
  divDef fun ti = def fun [divClause fun ti]

  export
  recipDef : Name -> (t : TypeInfo) -> {auto 0 _ : Record t} -> Decl
  recipDef fun ti = def fun [recipClause fun ti]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Fractional` for a
||| single-constructor data type.
export
Fractional : List Name -> ParamRecord -> List TopLevel
Fractional nms (Element p _) =
  let recip := funName p "recip"
      div   := funName p "divide"
      impl  := implName p "Fractional"
   in [ TL (recipClaim recip p) (recipDef nms recip p.info)
      , TL (divClaim div p) (divDef nms div p.info)
      , TL (fractionalImplClaim impl p) (fractionalImplDef div recip impl)
      ]

module Derive.Neg

import Derive.Record
import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
minusClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
minusClaim fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg) -> ~(arg)) (allImplicits p "Neg")
   in public' fun tpe

export
negClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
negClaim fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg)) (allImplicits p "Neg")
   in public' fun tpe

export
negImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
negImplClaim impl p = implClaim impl (implType "Neg" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

negImplDef : (neg, min, impl : Name) -> Decl
negImplDef neg min impl = def impl [var impl .= appNames "MkNeg" [neg, min]]

parameters (nms : List Name)
  minus : BoundArg 2 Explicit -> TTImp
  minus (BA arg [x,y] _)  = `(~(var x) - ~(var y))

  neg : BoundArg 1 Explicit -> TTImp
  neg (BA arg [x] _)  = `(negate ~(var x))

  export
  minusClause :
       (fun        : Name)
    -> (t          : TypeInfo)
    -> {auto 0 prf : Record t}
    -> Clause
  minusClause fun (MkTypeInfo n k as [c]) {prf = IsRecord} =
    let nx := freshNames "x" c.arty
        ny := freshNames "y" c.arty
        st := minus <$> boundArgs explicit c.args [nx,ny]
     in var fun .$ bindCon c nx .$ bindCon c ny .= appAll c.name (st <>> [])

  -- TODO: Less copy-paste
  export
  negClause :
       (fun        : Name)
    -> (t          : TypeInfo)
    -> {auto 0 prf : Record t}
    -> Clause
  negClause fun (MkTypeInfo n k as [c]) {prf = IsRecord} =
    let nx := freshNames "x" c.arty
        st := neg <$> boundArgs explicit c.args [nx]
     in var fun .$ bindCon c nx .= appAll c.name (st <>> [])

  export
  minusDef : Name -> (t : TypeInfo) -> {auto 0 _ : Record t} -> Decl
  minusDef fun ti = def fun [minusClause fun ti]

  export
  negDef : Name -> (t : TypeInfo) -> {auto 0 _ : Record t} -> Decl
  negDef fun ti = def fun [negClause fun ti]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Neg` for a
||| single-constructor data type.
export
Neg : List Name -> ParamRecord -> List TopLevel
Neg nms (Element p _) =
  let neg     := funName p "negate"
      minus   := funName p "minus"
      impl    := implName p "Neg"
   in [ TL (negClaim neg p) (negDef nms neg p.info)
      , TL (minusClaim minus p) (minusDef nms minus p.info)
      , TL (negImplClaim impl p) (negImplDef neg minus impl)
      ]

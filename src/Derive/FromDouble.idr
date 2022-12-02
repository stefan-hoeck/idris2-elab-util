module Derive.FromDouble

import Derive.Record
import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
fromDblClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
fromDblClaim fun p =
  let arg := p.applied
      tpe := piAll `(Double -> ~(arg)) (allImplicits p "FromDouble")
   in public' fun tpe

||| Top-level declaration implementing the `Eq` interface for
||| the given data type.
export
dblImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
dblImplClaim impl p = implClaim impl (implType "FromDouble" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

dblImplDef : (fd, impl : Name) -> Decl
dblImplDef fd impl = def impl [var impl .= appNames "MkFromDouble" [fd]]

parameters (nms : List Name)
  fromDbl : BoundArg 0 Explicit -> TTImp
  fromDbl (BA arg _ _) = `(fromDouble n)

  export
  fromDblClause :
       (fun        : Name)
    -> (t          : TypeInfo)
    -> {auto 0 prf : Record t}
    -> Clause
  fromDblClause fun (MkTypeInfo n k as [c]) {prf = IsRecord} =
    let st := fromDbl <$> boundArgs explicit c.args []
     in var fun .$ bindVar "n" .= appAll c.name (st <>> [])

  export
  fromDblDef : Name -> (t : TypeInfo) -> {auto 0 _ : Record t} -> Decl
  fromDblDef fun ti = def fun  [fromDblClause fun ti]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `FromDouble` for a
||| single-constructor data type.
export
FromDouble : List Name -> ParamRecord -> List TopLevel
FromDouble nms (Element p _) =
  let fromDbl := funName p "fromDouble"
      impl    := implName p "FromDouble"
   in [ TL (fromDblClaim fromDbl p) (fromDblDef nms fromDbl p.info)
      , TL (dblImplClaim impl p) (dblImplDef fromDbl impl)
      ]

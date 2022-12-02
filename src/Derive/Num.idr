module Derive.Num

import Derive.Record
import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Top-level declaration implementing used for `(+)` and `(*)` functions for
||| the given data type.
export
pmClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
pmClaim fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg) -> ~(arg)) (allImplicits p "Num")
   in public' fun tpe

||| Top-level declaration implementing used for the `fromInteger` function for
||| the given data type.
export
fromIntClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
fromIntClaim fun p =
  let arg := p.applied
      tpe := piAll `(Integer -> ~(arg)) (allImplicits p "Num")
   in public' fun tpe

||| Top-level declaration implementing the `Eq` interface for
||| the given data type.
export
numImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
numImplClaim impl p = implClaim impl (implType "Num" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

numImplDef : (p, m, fi, impl : Name) -> Decl
numImplDef p m fi impl = def impl [var impl .= appNames "MkNum" [p,m,fi]]

parameters (nms : List Name)
  plus : BoundArg 2 Explicit -> TTImp
  plus (BA arg [x,y] _)  = `(~(var x) + ~(var y))

  mult : BoundArg 2 Explicit -> TTImp
  mult (BA arg [x,y] _)  = `(~(var x) * ~(var y))

  fromInt : BoundArg 0 Explicit -> TTImp
  fromInt (BA arg _ _) = `(fromInteger n)

  export
  plusClause :
       (fun        : Name)
    -> (t          : TypeInfo)
    -> {auto 0 prf : Record t}
    -> Clause
  plusClause fun (MkTypeInfo n k as [c]) {prf = IsRecord} =
    let nx := freshNames "x" c.arty
        ny := freshNames "y" c.arty
        st := plus <$> boundArgs explicit c.args [nx,ny]
     in var fun .$ bindCon c nx .$ bindCon c ny .= appAll c.name (st <>> [])

  -- TODO: Less copy-paste
  export
  multClause :
       (fun        : Name)
    -> (t          : TypeInfo)
    -> {auto 0 prf : Record t}
    -> Clause
  multClause fun (MkTypeInfo n k as [c]) {prf = IsRecord} =
    let nx := freshNames "x" c.arty
        ny := freshNames "y" c.arty
        st := mult <$> boundArgs explicit c.args [nx,ny]
     in var fun .$ bindCon c nx .$ bindCon c ny .= appAll c.name (st <>> [])

  export
  fromIntClause :
       (fun        : Name)
    -> (t          : TypeInfo)
    -> {auto 0 prf : Record t}
    -> Clause
  fromIntClause fun (MkTypeInfo n k as [c]) {prf = IsRecord} =
    let st := fromInt <$> boundArgs explicit c.args []
     in var fun .$ bindVar "n" .= appAll c.name (st <>> [])

  export
  plusDef : Name -> (t : TypeInfo) -> {auto 0 _ : Record t} -> Decl
  plusDef fun ti = def fun [plusClause fun ti]

  export
  multDef : Name -> (t : TypeInfo) -> {auto 0 _ : Record t} -> Decl
  multDef fun ti = def fun [multClause fun ti]

  export
  fromIntDef : Name -> (t : TypeInfo) -> {auto 0 _ : Record t} -> Decl
  fromIntDef fun ti = def fun  [fromIntClause fun ti]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Num` for a
||| single-constructor data type.
export
Num : List Name -> ParamRecord -> List TopLevel
Num nms (Element p _) =
  let mult    := funName p "mult"
      plus    := funName p "plus"
      fromInt := funName p "fromInt"
      impl    := implName p "Num"
   in [ TL (pmClaim plus p) (plusDef nms plus p.info)
      , TL (pmClaim mult p) (multDef nms mult p.info)
      , TL (fromIntClaim fromInt p) (fromIntDef nms fromInt p.info)
      , TL (numImplClaim impl p) (numImplDef plus mult fromInt impl)
      ]

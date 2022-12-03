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

plus : BoundArg 2 Explicit -> TTImp
plus (BA arg [x,y] _)  = `(~(x) + ~(y))

mult : BoundArg 2 Explicit -> TTImp
mult (BA arg [x,y] _)  = `(~(x) * ~(y))

fromInt : BoundArg 0 Explicit -> TTImp
fromInt _ = `(fromInteger n)

export
plusDef : Name -> Con n vs -> Decl
plusDef fun c =
  let clause := mapArgs2 explicit (\x,y => var fun .$ x .$ y) plus c
   in def fun [clause]

export
multDef : Name -> Con n vs -> Decl
multDef fun c =
  let clause := mapArgs2 explicit (\x,y => var fun .$ x .$ y) mult c
   in def fun [clause]

export
fromIntDef : Name -> Con n vs -> Decl
fromIntDef f c = def f [var f .$ `(n) .= injArgs explicit fromInt c]

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
      con     := getConstructor p.info
   in [ TL (pmClaim plus p) (plusDef plus con)
      , TL (pmClaim mult p) (multDef mult con)
      , TL (fromIntClaim fromInt p) (fromIntDef fromInt con)
      , TL (numImplClaim impl p) (numImplDef plus mult fromInt impl)
      ]

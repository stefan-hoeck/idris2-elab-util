module Derive.Num

import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Top-level declaration implementing used for `(+)` and `(*)` functions for
||| the given data type.
export
pmClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
pmClaim vis fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg) -> ~(arg)) (allImplicits p "Num")
   in simpleClaim vis fun tpe

||| Top-level declaration implementing used for the `fromInteger` function for
||| the given data type.
export
fromIntClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
fromIntClaim vis fun p =
  let arg := p.applied
      tpe := piAll `(Integer -> ~(arg)) (allImplicits p "Num")
   in simpleClaim vis fun tpe

||| Top-level declaration implementing the `Eq` interface for
||| the given data type.
export
numImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
numImplClaim v impl p = implClaimVis v impl (implType "Num" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

numImplDef : (p, m, fi, impl : Name) -> Decl
numImplDef p m fi impl =
  def impl [patClause (var impl) (appNames "MkNum" [p,m,fi])]

plus : BoundArg 2 Explicit -> TTImp
plus (BA arg [x,y] _)  = `(~(varStr x) + ~(varStr y))

mult : BoundArg 2 Explicit -> TTImp
mult (BA arg [x,y] _)  = `(~(varStr x) * ~(varStr y))

fromInt : BoundArg 0 Explicit -> TTImp
fromInt _ = `(fromInteger n)

export
plusDef : Name -> Con n vs -> Decl
plusDef fun c =
  let clause := mapArgs2 explicit (\x,y => `(~(var fun) ~(x) ~(y))) plus c
   in def fun [clause]

export
multDef : Name -> Con n vs -> Decl
multDef fun c =
  let clause := mapArgs2 explicit (\x,y => `(~(var fun) ~(x) ~(y))) mult c
   in def fun [clause]

export
fromIntDef : Name -> Con n vs -> Decl
fromIntDef f c =
  def f [patClause `(~(var f) n) (injArgs explicit fromInt c)]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Num` for a
||| single-constructor data type.
export
NumVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
NumVis vis nms p = case p.info.cons of
  [c] =>
    let mult    := funName p "mult"
        plus    := funName p "plus"
        fromInt := funName p "fromInt"
        impl    := implName p "Num"
     in Right
          [ TL (pmClaim vis plus p) (plusDef plus c)
          , TL (pmClaim vis mult p) (multDef mult c)
          , TL (fromIntClaim vis fromInt p) (fromIntDef fromInt c)
          , TL (numImplClaim vis impl p) (numImplDef plus mult fromInt impl)
          ]
  _   => failRecord "Num"

||| Alias for `NumVis Public`
export %inline
Num : List Name -> ParamTypeInfo -> Res (List TopLevel)
Num = NumVis Public

||| Generate a single `fromInteger` function for the given type
export
FromIntegerVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
FromIntegerVis vis nms p = case p.info.cons of
  [c] =>
    let fun := the Name "fromInteger"
     in Right [ TL (fromIntClaim vis fun p) (fromIntDef fun c) ]
  _   => failRecord "fromInteger"

||| Generate a single `fromInteger` function with `public export`
||| visibility for the given type
export %inline
FromInteger : List Name -> ParamTypeInfo -> Res (List TopLevel)
FromInteger = FromIntegerVis Public

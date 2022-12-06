module Derive.Neg

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

minus : BoundArg 2 Explicit -> TTImp
minus (BA arg [x,y] _)  = `(~(varStr x) - ~(varStr y))

neg : BoundArg 1 Explicit -> TTImp
neg (BA arg [x] _)  = `(negate ~(varStr x))

export
minusDef : Name -> Con n vs -> Decl
minusDef fun c =
  let clause := mapArgs2 explicit (\x,y => var fun .$ x .$ y) minus c
   in def fun [clause]

export
negDef : Name -> Con n vs -> Decl
negDef fun c =
  let clause := mapArgs explicit (var fun .$) neg c
   in def fun [clause]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Neg` for a
||| single-constructor data type.
export
Neg : List Name -> ParamTypeInfo -> Res (List TopLevel)
Neg nms p = case p.info.cons of
  [c] =>
    let neg   := funName p "negate"
        minus := funName p "minus"
        impl  := implName p "Neg"
     in Right [ TL (negClaim neg p) (negDef neg c)
              , TL (minusClaim minus p) (minusDef minus c)
              , TL (negImplClaim impl p) (negImplDef neg minus impl)
              ]
  _   => failRecord "Neg"

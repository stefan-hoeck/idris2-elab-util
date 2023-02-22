module Derive.Neg

import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
minusClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
minusClaim vis fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg) -> ~(arg)) (allImplicits p "Neg")
   in simpleClaim vis fun tpe

export
negClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
negClaim vis fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg)) (allImplicits p "Neg")
   in simpleClaim vis fun tpe

export
negImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
negImplClaim v impl p = implClaimVis v impl (implType "Neg" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

negImplDef : (neg, min, impl : Name) -> Decl
negImplDef neg min impl =
  def impl [patClause (var impl) (appNames "MkNeg" [neg, min])]

minus : BoundArg 2 Explicit -> TTImp
minus (BA arg [x,y] _)  = `(~(varStr x) - ~(varStr y))

neg : BoundArg 1 Explicit -> TTImp
neg (BA arg [x] _)  = `(negate ~(varStr x))

export
minusDef : Name -> Con n vs -> Decl
minusDef fun c =
  let clause := mapArgs2 explicit (\x,y => `(~(var fun) ~(x) ~(y))) minus c
   in def fun [clause]

export
negDef : Name -> Con n vs -> Decl
negDef fun c =
  let clause := mapArgs explicit (var fun `app`) neg c
   in def fun [clause]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Neg` for a
||| single-constructor data type.
export
NegVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
NegVis vis nms p = case p.info.cons of
  [c] =>
    let neg   := funName p "negate"
        minus := funName p "minus"
        impl  := implName p "Neg"
     in Right [ TL (negClaim vis neg p) (negDef neg c)
              , TL (minusClaim vis minus p) (minusDef minus c)
              , TL (negImplClaim vis impl p) (negImplDef neg minus impl)
              ]
  _   => failRecord "Neg"

||| Alias for `NegVis Public`
export %inline
Neg : List Name -> ParamTypeInfo -> Res (List TopLevel)
Neg = NegVis Public

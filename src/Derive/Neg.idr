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

minus : BoundArg 2 Explicit -> TTImp
minus (BA arg [x,y] _)  = `(~(x) - ~(y))

neg : BoundArg 1 Explicit -> TTImp
neg (BA arg [x] _)  = `(negate ~(x))

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
Neg : List Name -> ParamRecord -> List TopLevel
Neg _ (Element p _) =
  let neg   := funName p "negate"
      minus := funName p "minus"
      impl  := implName p "Neg"
      con   := getConstructor p.info
   in [ TL (negClaim neg p) (negDef neg con)
      , TL (minusClaim minus p) (minusDef minus con)
      , TL (negImplClaim impl p) (negImplDef neg minus impl)
      ]

module Derive.Abs

import Derive.Record
import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
absClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
absClaim fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg)) (allImplicits p "Abs")
   in public' fun tpe

export
absImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
absImplClaim impl p = implClaim impl (implType "Abs" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

absImplDef : (abs, impl : Name) -> Decl
absImplDef abs impl = def impl [var impl .= appNames "MkAbs" [abs]]

parameters (nms : List Name)
  abs : BoundArg 1 Explicit -> TTImp
  abs (BA arg [x] _)  = `(abs ~(var x))

  -- TODO: Less copy-paste
  export
  absClause :
       (fun        : Name)
    -> (t          : TypeInfo)
    -> {auto 0 prf : Record t}
    -> Clause
  absClause fun (MkTypeInfo n k as [c]) {prf = IsRecord} =
    let nx := freshNames "x" c.arty
        st := abs <$> boundArgs explicit c.args [nx]
     in var fun .$ bindCon c nx .= appAll c.name (st <>> [])

  export
  absDef : Name -> (t : TypeInfo) -> {auto 0 _ : Record t} -> Decl
  absDef fun ti = def fun [absClause fun ti]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Abs` for a
||| single-constructor data type.
export
Abs : List Name -> ParamRecord -> List TopLevel
Abs nms (Element p _) =
  let abs     := funName p "abs"
      impl    := implName p "Abs"
   in [ TL (absClaim abs p) (absDef nms abs p.info)
      , TL (absImplClaim impl p) (absImplDef abs impl)
      ]


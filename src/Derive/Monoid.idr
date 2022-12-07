module Derive.Monoid

import public Language.Reflection.Derive

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Top-level function declaration implementing the `neutral` function for
||| the given data type.
export
neutralClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
neutralClaim fun p =
  let arg := p.applied
      tpe := piAll arg (allImplicits p "Monoid")
   in public' fun tpe

||| Top-level declaration implementing the `Semigroup` interface for
||| the given data type.
export
monoidImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
monoidImplClaim impl p = implClaim impl (implType "Monoid" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
monoidImplDef : (fun, impl : Name) -> Decl
monoidImplDef f i = def i [var i .= var "MkMonoid" .$ var f]

rhs : Con n vs -> TTImp
rhs = injArgs explicit (const `(neutral))

||| Definition of a (local or top-level) function implementing
||| the neutral operation.
export
neutralDef : Name -> Con n vs -> Decl
neutralDef f c = def f [var f .= rhs c]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Semigroup` for a given data type.
export
Monoid : List Name -> ParamTypeInfo -> Res (List TopLevel)
Monoid nms p = case p.info.cons of
  [c] =>
    let fun  := funName p "neutral"
        impl := implName p "Monoid"
     in Right [ TL (neutralClaim fun p) (neutralDef fun c)
              , TL (monoidImplClaim impl p) (monoidImplDef fun impl)
              ]
  _   => failRecord "Monoid"

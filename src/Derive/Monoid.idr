module Derive.Monoid

import public Derive.Record
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

||| Derive an implementation of `Semigroup a` for a custom data type `a`.
|||
||| Use this, if you need custom constraints in your implementation.
export %macro
deriveMonoid : Elab (Eq f)
deriveMonoid = do
  Just tpe <- goal
    | Nothing => fail "Can't infer goal"
  let Just (resTpe, nm) := extractResult tpe
    | Nothing => fail "Invalid goal type: \{show tpe}"
  Element t _  <- find (Subset TypeInfo Record) nm

  let impl := rhs (getConstructor t)

  logMsg "derive.definitions" 1 $ show impl
  check $ var "MkMonoid" .$ impl

||| Generate declarations and implementations for `Semigroup` for a given data type.
export
Monoid : List Name -> ParamRecord -> List TopLevel
Monoid _ (Element p _) =
  let fun  := funName p "neutral"
      impl := implName p "Monoid"
   in [ TL (neutralClaim fun p) (neutralDef fun $ getConstructor p.info)
      , TL (monoidImplClaim impl p) (monoidImplDef fun impl)
      ]

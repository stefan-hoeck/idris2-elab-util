module Derive.Monoid

import public Derive.Record
import public Language.Reflection.Derive

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Name of the top-level function implementing the `neutral` function
public export
(.neutralName) : Named a => a -> Name
v.neutralName = UN $ Basic "neutral\{v.nameStr}"

||| Top-level function declaration implementing the `neutral` function for
||| the given data type.
export
neutralClaim : (p : ParamTypeInfo) -> Decl
neutralClaim p =
  let arg := p.applied
      tpe := piAll arg (allImplicits p "Monoid")
   in public' p.neutralName tpe

||| Name of the derived interface implementation.
public export
(.monoidImplName) : Named a => a -> Name
v.monoidImplName = UN $ Basic "monoidImpl\{v.nameStr}"

||| Top-level declaration implementing the `Semigroup` interface for
||| the given data type.
export
monoidImplClaim : (p : ParamTypeInfo) -> {auto 0 _ : ParamRecord p} -> Decl
monoidImplClaim p = implClaim p.monoidImplName (implType "Monoid" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
monoidImplDef : (p : ParamTypeInfo) -> Decl
monoidImplDef p =
  let impl := p.monoidImplName
   in def impl [var impl .= var "MkMonoid" .$ var p.neutralName]

-- Generate set of constructor arguments.
neutralRHS : Name -> SnocList TTImp -> Vect n Arg -> TTImp
neutralRHS n st (x :: xs) = case isExplicit x of
  True  => neutralRHS n (st :< `(neutral)) xs
  False => neutralRHS n st xs
neutralRHS n sx [] = appAll n (sx <>> [])

export
neutralClause :
     (fun        : Name)
  -> (t          : TypeInfo)
  -> {auto 0 prf : Record t}
  -> Clause
neutralClause fun t =
  let c := getConstructor t
   in var fun .= neutralRHS c.name Lin c.args

||| Definition of a (local or top-level) function implementing
||| the neutral operation.
export
neutralDef : Name -> (t : TypeInfo) -> {auto 0 _ : Record t} -> Decl
neutralDef fun ti = def fun [neutralClause fun ti]

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

  let c    := getConstructor t
      impl := neutralRHS c.name Lin c.args

  logMsg "derive.definitions" 1 $ show impl
  check $ var "MkSemigroup" .$ impl

||| Generate declarations and implementations for `Semigroup` for a given data type.
export
Monoid : List Name -> Subset ParamTypeInfo ParamRecord -> List TopLevel
Monoid _ (Element p _) =
  [ TL (neutralClaim p) (neutralDef p.neutralName p.info)
  , TL (monoidImplClaim p) (monoidImplDef p)
  ]

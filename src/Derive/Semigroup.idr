module Derive.Semigroup

import public Derive.Record
import public Language.Reflection.Derive

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Name of the top-level function implementing the append function
public export
(.appName) : Named a => a -> Name
v.appName = UN $ Basic "app\{v.nameStr}"

||| Top-level function declaration implementing the append function for
||| the given data type.
export
appClaim : (p : ParamTypeInfo) -> Decl
appClaim p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg) -> ~(arg)) (allImplicits p "Semigroup")
   in public' p.appName tpe

||| Name of the derived interface implementation.
public export
(.semigroupImplName) : Named a => a -> Name
v.semigroupImplName = UN $ Basic "semigroupImpl\{v.nameStr}"

||| Top-level declaration implementing the `Semigroup` interface for
||| the given data type.
export
semigroupImplClaim : (p : ParamTypeInfo) -> {auto 0 _ : ParamRecord p} -> Decl
semigroupImplClaim p = implClaim p.semigroupImplName (implType "Semigroup" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
semigroupImplDef : (p : ParamTypeInfo) -> Decl
semigroupImplDef p =
  let impl := p.semigroupImplName
   in def impl [var impl .= var "MkSemigroup" .$ var p.appName]

parameters (nms : List Name)
  -- Append set of constructor arguments.
  -- Checks if the argument types are safely recursive, that is, contains
  -- one of the data type names listed in `nms`. If so, prefixes
  -- the generated function call with `assert_total`.
  appRHS :
       Name
    -> SnocList TTImp
    -> Vect n Arg
    -> Vect n Name
    -> Vect n Name
    -> TTImp
  appRHS n st (x :: xs) (y :: ys) (z :: zs) = case isExplicit x of
    True  =>
      let t := assertIfRec nms x.type `(~(var y) <+> ~(var z))
       in appRHS n (st :< t) xs ys zs
    False => appRHS n st xs ys zs
  appRHS n sx [] [] [] = appAll n (sx <>> [])

  ||| Generates pattern match clauses for the constructors of
  ||| the given data type. `fun` is the name of the function we implement.
  ||| This is either a local function definition in case of a
  ||| custom derivation, or the name of a top-level function.
  export
  appClause :
       (fun        : Name)
    -> (t          : TypeInfo)
    -> {auto 0 prf : Record t}
    -> Clause
  appClause fun (MkTypeInfo n k as [c]) {prf = IsRecord} =
    let nx    := freshNames "x" c.arty
        ny    := freshNames "y" c.arty
     in var fun .$ bindCon c nx .$ bindCon c ny .=
        appRHS c.name Lin c.args nx ny

  ||| Definition of a (local or top-level) function implementing
  ||| the append operation.
  export
  appDef : Name -> (t : TypeInfo) -> {auto 0 _ : Record t} -> Decl
  appDef fun ti = def fun [appClause fun ti]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Derive an implementation of `Semigroup a` for a custom data type `a`.
|||
||| Use this, if you need custom constraints in your implementation.
export %macro
deriveSemigroup : Elab (Eq f)
deriveSemigroup = do
  Just tpe <- goal
    | Nothing => fail "Can't infer goal"
  let Just (resTpe, nm) := extractResult tpe
    | Nothing => fail "Invalid goal type: \{show tpe}"
  Element ti _  <- find (Subset TypeInfo Record) nm

  let impl :=  lambdaArg {a = Name} "x"
           .=> lambdaArg {a = Name} "y"
           .=> iCase `(MkPair x y) implicitFalse [appClause [ti.name] "MkPair" ti]

  logMsg "derive.definitions" 1 $ show impl
  check $ var "MkSemigroup" .$ impl

||| Generate declarations and implementations for `Semigroup` for a given data type.
export
Semigroup : List Name -> Subset ParamTypeInfo ParamRecord -> List TopLevel
Semigroup nms (Element p _) =
  [ TL (appClaim p) (appDef nms p.appName p.info)
  , TL (semigroupImplClaim p) (semigroupImplDef p)
  ]

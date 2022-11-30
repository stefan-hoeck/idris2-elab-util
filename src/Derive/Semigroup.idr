module Derive.Semigroup

import public Derive.Record
import public Language.Reflection.Derive

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Top-level function declaration implementing the append function for
||| the given data type.
export
appClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
appClaim fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg) -> ~(arg)) (allImplicits p "Semigroup")
   in public' fun tpe

||| Top-level declaration implementing the `Semigroup` interface for
||| the given data type.
export
semigroupImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
semigroupImplClaim impl p = implClaim impl (implType "Semigroup" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
semigroupImplDef : (fun, impl : Name) -> Decl
semigroupImplDef f i = def i [var i .= var "MkSemigroup" .$ var f]

parameters (nms : List Name)
  ttimp : BoundArg 2 Regular -> TTImp
  ttimp (BA arg [x,y] _) = assertIfRec nms arg.type `(~(var x) <+> ~(var y))

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
    let nx := freshNames "x" c.arty
        ny := freshNames "y" c.arty
        st := ttimp <$> boundArgs regular c.args [nx,ny]
     in var fun .$ bindCon c nx .$ bindCon c ny .= appAll c.name (st <>> [])

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
Semigroup : List Name -> ParamRecord -> List TopLevel
Semigroup nms (Element p _) =
  let fun  := funName p "append"
      impl := implName p "Semigroup"
   in [ TL (appClaim fun p) (appDef nms fun p.info)
      , TL (semigroupImplClaim impl p) (semigroupImplDef fun impl)
      ]

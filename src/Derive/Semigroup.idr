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

app : BoundArg 2 Explicit -> TTImp
app (BA _ [x,y] _) = `(~(x) <+> ~(y))

appClause : Name -> Con n vs -> Clause
appClause f = mapArgs2 explicit (\x,y => var f .$ x .$ y) app

export
appDef : Name -> Con n vs -> Decl
appDef f c = def f [appClause f c]

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
           .=> iCase `(MkPair x y) implicitFalse
                 [appClause "MkPair" $ getConstructor ti]

  logMsg "derive.definitions" 1 $ show impl
  check $ var "MkSemigroup" .$ impl

||| Generate declarations and implementations for `Semigroup` for a given data type.
export
Semigroup : List Name -> ParamRecord -> List TopLevel
Semigroup nms (Element p _) =
  let fun  := funName p "append"
      impl := implName p "Semigroup"
   in [ TL (appClaim fun p) (appDef fun $ getConstructor p.info)
      , TL (semigroupImplClaim impl p) (semigroupImplDef fun impl)
      ]

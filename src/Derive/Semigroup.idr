module Derive.Semigroup

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

||| Generate declarations and implementations for `Semigroup` for a given data type.
export
Semigroup : List Name -> ParamTypeInfo -> Res (List TopLevel)
Semigroup nms p = case p.info.cons of
  [c] =>
    let fun  := funName p "append"
        impl := implName p "Semigroup"
     in Right [ TL (appClaim fun p) (appDef fun c)
              , TL (semigroupImplClaim impl p) (semigroupImplDef fun impl)
              ]
  _   => failRecord "Semigroup"

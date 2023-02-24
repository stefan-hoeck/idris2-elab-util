module Derive.Semigroup

import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Top-level function declaration implementing the append function for
||| the given data type.
export
appClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
appClaim vis fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg) -> ~(arg)) (allImplicits p "Semigroup")
   in simpleClaim vis fun tpe

||| Top-level declaration implementing the `Semigroup` interface for
||| the given data type.
export
semigroupImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
semigroupImplClaim v impl p = implClaimVis v impl (implType "Semigroup" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
semigroupImplDef : (fun, impl : Name) -> Decl
semigroupImplDef f i =
  def i [patClause (var i) (var "MkSemigroup" `app` var f)]

app : BoundArg 2 Explicit -> TTImp
app (BA _ [x,y] _) = `(~(varStr x) <+> ~(varStr y))

appClause : Name -> Con n vs -> Clause
appClause f = mapArgs2 explicit (\x,y => `(~(var f) ~(x) ~(y))) app

export
appDef : Name -> Con n vs -> Decl
appDef f c = def f [appClause f c]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Semigroup` for a given data type.
export
SemigroupVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
SemigroupVis vis nms p = case p.info.cons of
  [c] =>
    let fun  := funName p "append"
        impl := implName p "Semigroup"
     in Right [ TL (appClaim vis fun p) (appDef fun c)
              , TL (semigroupImplClaim vis impl p) (semigroupImplDef fun impl)
              ]
  _   => failRecord "Semigroup"

||| Alias for `SemigroupVis Public`
export %inline
Semigroup : List Name -> ParamTypeInfo -> Res (List TopLevel)
Semigroup = SemigroupVis Public

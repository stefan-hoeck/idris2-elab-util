module Derive.Pretty

import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Name of the top-level function implementing the derived `prettyPrec` function.
public export
(.prettyName) : Named a => a -> Name
v.prettyName = UN $ Basic "pretty\{v.nameStr}"

||| General type of a `prettyPrec` function with the given list
||| of implicit and auto-implicit arguments, plus the given argument type
||| to be displayed.
export
generalPrettyType : (implicits : List Arg) -> (arg : TTImp) -> TTImp
generalPrettyType is arg = piAll `(Prec -> ~(arg) -> Doc ann) is

||| Top-level function declaration implementing the `prettyPrec` function for
||| the given data type.
export
prettyClaim : Visibility -> (p : ParamTypeInfo) -> Decl
prettyClaim vis p =
  let tpe := generalPrettyType (allImplicits p "Pretty") p.applied
   in simpleClaim vis p.prettyName tpe

||| Name of the derived interface implementation.
public export
(.prettyImplName) : Named a => a -> Name
v.prettyImplName = UN $ Basic "prettyImpl\{v.nameStr}"

||| Top-level declaration of the `Pretty` implementation for the given data type.
export
prettyImplClaim : Visibility -> (p : ParamTypeInfo) -> Decl
prettyImplClaim v p =
  let tpe := piAll (var "Pretty" .$ p.applied) (allImplicits p "Pretty")
   in implClaimVis v p.prettyImplName tpe

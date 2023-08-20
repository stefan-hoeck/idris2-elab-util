module Derive.Pretty

import public Text.PrettyPrint.Bernardy
import Language.Reflection.Util
import public Derive.Show

%default total

public export
data PlaceHolder = US

public export
Pretty PlaceHolder where
  prettyPrec _ _ = symbol '_'

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| General type of a `prettyPrec` function with the given list
||| of implicit and auto-implicit arguments, plus the given argument type
||| to be displayed.
export
generalPrettyType : (implicits : List Arg) -> (arg : TTImp) -> TTImp
generalPrettyType is arg =
  piAll `({opts : LayoutOpts} -> Prec -> ~(arg) -> Doc opts) is

||| Top-level function declaration implementing the `prettyPrec` function for
||| the given data type.
export
prettyClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
prettyClaim vis fun p =
  simpleClaim vis fun (generalPrettyType (allImplicits p "Pretty") p.applied)

||| Top-level declaration of the `Pretty` implementation for the given data type.
export
prettyImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
prettyImplClaim v impl p = implClaimVis v impl (implType "Pretty" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

||| Top-level definition of the `Pretty` implementation for the given data type.
export
prettyImplDef : (fun, impl : Name) -> Decl
prettyImplDef f i = def i [patClause (var i) (var "MkPretty" `app` var f)]

pvar : TTImp
pvar = var "p"

parameters (nms : List Name)
  -- pretty printing a single, explicit, unnamed constructor argument
  arg : BoundArg 1 Explicit -> TTImp
  arg (BA (MkArg M0 _ _ _) _   _) = `(pretty US)
  arg (BA (MkArg _  _ _ t) [x] _) = assertIfRec nms t `(prettyArg ~(varStr x))

  -- prettying a constructor plus its arguments
  rhs : Name -> SnocList TTImp -> TTImp
  rhs n st  = `(prettyCon p ~(n.namePrim) ~(listOf st))

  -- prettying a single, explicit, named constructor argument
  narg : BoundArg 1 NamedExplicit -> TTImp
  narg (BA a [x]   _) =
    let nm := (argName a).namePrim
     in case a.count of
       M0 => `(prettyField ~(nm) US)
       _  => assertIfRec nms a.type `(prettyField ~(nm) ~(varStr x))

  -- prettying a constructor plus its named arguments
  nrhs : Name -> SnocList TTImp -> TTImp
  nrhs n st  = `(prettyRecord p ~(n.namePrim) ~(listOf st))

  export
  prettyClauses : (fun : Maybe Name) -> TypeInfo -> List Clause
  prettyClauses fun ti = map clause ti.cons

    where
      lhs : TTImp -> TTImp
      lhs bc = maybe bc (\x => `(~(var x) ~(pvar) ~(bc))) fun

      clause : Con ti.arty ti.args -> Clause
      clause c = case all namedArg c.args of
        True  => accumArgs namedExplicit lhs (nrhs c.name) narg c
        False => accumArgs explicit lhs (rhs c.name) arg c

  export
  prettyDef : Name -> TypeInfo -> Decl
  prettyDef fun ti = def fun (prettyClauses (Just fun) ti)

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Derive an implementation of `Pretty a` for a custom data type `a`.
|||
||| Note: This is mainly to be used for indexed data types. Consider using
|||       `derive` together with `Derive.Pretty.Pretty` for parameterized data types.
export %macro
derivePretty : Elab (Pretty f)
derivePretty = do
  Just tpe <- goal
    | Nothing => fail "Can't infer goal"
  let Just (resTpe, nm) := extractResult tpe
    | Nothing => fail "Invalid goal type: \{show tpe}"
  ti <- getInfo' nm

  let impl :=
        lam (lambdaArg {a = Name} "p") $
        lam (lambdaArg {a = Name} "x") $
        iCase `(x) implicitFalse (prettyClauses [ti.name] Nothing ti)

  logTerm "derive.definitions" 1 "pretty implementation" impl
  check $ var "MkPretty" `app` impl

||| Generate declarations and implementations for `Pretty` for a given data type.
export
PrettyVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
PrettyVis vis nms p =
  let fun  := funName p "prettyPrec"
      impl := implName p "Pretty"
   in Right
        [ TL (prettyClaim vis fun p) (prettyDef nms fun p.info)
        , TL (prettyImplClaim vis impl p) (prettyImplDef fun impl)
        ]

||| Alias for `PrettyVis Public`
export %inline
Pretty : List Name -> ParamTypeInfo -> Res (List TopLevel)
Pretty = PrettyVis Public

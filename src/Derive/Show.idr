module Derive.Show

import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export
conWithArgs : Prec -> String -> List String -> String
conWithArgs p str [] = str
conWithArgs p str ss = showCon p str $ concat ss

public export
recordWithArgs : Prec -> String -> List (String,String) -> String
recordWithArgs p str [] = str
recordWithArgs p str ss =
  let args := concat $ intersperse ", " $ map (\(n,v) => "\{n} = \{v}") ss
   in showCon p str $ " {\{args}}"

--------------------------------------------------------------------------------
--          Named Constructors
--------------------------------------------------------------------------------

||| Checks, if the given argument is properly named.
public export
namedArg : (a : Arg) -> Bool
namedArg (MkArg _ ExplicitArg (Just $ UN _) _) = True
namedArg (MkArg _ ExplicitArg _ _)             = False
namedArg (MkArg _ ImplicitArg _ _)             = True
namedArg (MkArg _ AutoImplicit _ _)            = True
namedArg (MkArg _ (DefImplicit _) _ _)         = True

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| General type of a `showPrec` function with the given list
||| of implicit and auto-implicit arguments, plus the given argument type
||| to be displayed.
export
generalShowType : (implicits : List Arg) -> (arg : TTImp) -> TTImp
generalShowType is arg = piAll `(Prec -> ~(arg) -> String) is

||| Top-level function declaration implementing the `showPrec` function for
||| the given data type.
export
showClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
showClaim vis fun p =
  simpleClaim vis fun (generalShowType (allImplicits p "Show") p.applied)

||| Top-level declaration of the `Show` implementation for the given data type.
export
showImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
showImplClaim v impl p = implClaimVis v impl (implType "Show" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

||| Top-level definition of the `Show` implementation for the given data type.
export
showImplDef : (fun, impl : Name) -> Decl
showImplDef f i = def i [var i .= var "mkShowPrec" .$ var f]

pvar : TTImp
pvar = var "p"

parameters (nms : List Name)
  -- showing a single, explicit, unnamed constructor argument
  arg : BoundArg 1 Explicit -> TTImp
  arg (BA (MkArg M0 _ _ _) _   _) = primVal (Str " _")
  arg (BA (MkArg _  _ _ t) [x] _) = assertIfRec nms t `(showArg ~(varStr x))

  -- showing a constructor plus its arguments
  rhs : Name -> SnocList TTImp -> TTImp
  rhs n [<] = n.namePrim
  rhs n st  = `(conWithArgs p ~(n.namePrim) ~(listOf st))

  -- showing a single, explicit, named constructor argument
  narg : BoundArg 1 NamedExplicit -> TTImp
  narg (BA a [x]   _) =
    let nm := (argName a).namePrim
     in case a.count of
       M0 => `(MkPair ~(nm) "_")
       _  =>
         let shown := assertIfRec nms a.type `(show ~(varStr x))
          in `(MkPair ~(nm) ~(shown))

  -- showing a constructor plus its named arguments
  nrhs : Name -> SnocList TTImp -> TTImp
  nrhs n [<] = n.namePrim
  nrhs n st  = `(recordWithArgs p ~(n.namePrim) ~(listOf st))

  export
  showClauses : (fun : Maybe Name) -> TypeInfo -> List Clause
  showClauses fun ti = map clause ti.cons
    where
      lhs : TTImp -> TTImp
      lhs bc = maybe bc ((.$ pvar .$ bc) . var) fun

      clause : Con ti.arty ti.args -> Clause
      clause c = case all namedArg c.args of
        True  => accumArgs namedExplicit lhs (nrhs c.name) narg c
        False => accumArgs explicit lhs (rhs c.name) arg c

  export
  showDef : Name -> TypeInfo -> Decl
  showDef fun ti = def fun (showClauses (Just fun) ti)

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Derive an implementation of `Show a` for a custom data type `a`.
|||
||| Note: This is mainly to be used for indexed data types. Consider using
|||       `derive` together with `Derive.Show.Show` for parameterized data types.
export %macro
deriveShow : Elab (Show f)
deriveShow = do
  Just tpe <- goal
    | Nothing => fail "Can't infer goal"
  let Just (resTpe, nm) := extractResult tpe
    | Nothing => fail "Invalid goal type: \{show tpe}"
  ti <- getInfo' nm

  let impl :=
           lam (lambdaArg {a = Name} "p") $
           lam (lambdaArg {a = Name} "x") $
           iCase `(x) implicitFalse (showClauses [ti.name] Nothing ti)

  logMsg "derive.definitions" 1 $ show impl
  check $ var "mkShowPrec" .$ impl

||| Generate declarations and implementations for `Show` for a given data type.
export
ShowVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
ShowVis vis nms p =
  let fun  := funName p "showPrec"
      impl := implName p "Show"
   in Right [ TL (showClaim vis fun p) (showDef nms fun p.info)
            , TL (showImplClaim vis impl p) (showImplDef fun impl)
            ]

||| Alias for `ShowVis Public`
export %inline
Show : List Name -> ParamTypeInfo -> Res (List TopLevel)
Show = ShowVis Public

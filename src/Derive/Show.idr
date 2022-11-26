module Derive.Show

import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Name of the top-level function implementing the derived show function.
public export
(.showName) : Named a => a -> Name
v.showName = UN $ Basic "show\{v.nameStr}"

||| General type of a `showPrec` function with the given list
||| of implicit and auto-implicit arguments, plus the given argument type
||| to be displayed.
export
generalShowType : (implicits : List Arg) -> (arg : TTImp) -> TTImp
generalShowType is arg = piAll `(Prec -> ~(arg) -> String) is

||| Top-level function declaration implementing the `showPrec` function for
||| the given data type.
export
showClaim : (p : ParamTypeInfo) -> Decl
showClaim p =
  let tpe := generalShowType (allImplicits p "Show") p.applied
   in public' p.showName tpe

||| Name of the derived interface implementation.
public export
(.showImplName) : Named a => a -> Name
v.showImplName = UN $ Basic "showImpl\{v.nameStr}"

||| Top-level declaration of the `Show` implementation for the given data type.
export
showImplClaim : (p : ParamTypeInfo) -> Decl
showImplClaim p = implClaim p.showImplName (implType "Show" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

||| Top-level definition of the `Show` implementation for the given data type.
export
showImplDef : Named a => a -> Decl
showImplDef p =
  def p.showImplName [var p.showImplName .= var "mkShowPrec" .$ var p.showName]

pvar : TTImp
pvar = var "p"

parameters (nms : List Name)

  -- String conversion for a set of constructor arguments.
  -- Checks if the argument types are safely recursive, that is, contains
  -- one of the data type names listed in `nms`. If so, prefixes
  -- the generated function call with `assert_total`.
  showRHS : Name -> SnocList TTImp -> Vect n Arg -> Vect n Name -> TTImp
  showRHS n st (x :: xs) (y :: ys) = case isExplicit x of
    True  => case x.count of
      M0 => primVal (Str " _")
      _  => let t := assertIfRec nms x.type `(showArg ~(var y))
             in showRHS n (st :< t) xs ys
    False => showRHS n st xs ys
  showRHS n Lin []        [] = n.namePrim
  showRHS n sx  []        [] =
    let args := foldr (\e,acc => `(~(e) :: ~(acc))) `(Prelude.Nil) sx
     in var "showCon" .$ pvar .$ n.namePrim .$ `(concat ~(args))

  export
  showClauses : (fun : Maybe Name) -> TypeInfo -> List Clause
  showClauses fun ti = map clause ti.cons
    where clause : Con ti.arty ti.args -> Clause
          clause c =
            let ns  := freshNames "x" c.arty
                bc  := bindCon c ns
                lhs := maybe bc ((.$ pvar .$ bc) . var) fun
             in lhs .= showRHS c.name Lin c.args ns

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

  let impl :=  lambdaArg {a = Name} "p"
           .=> lambdaArg {a = Name} "x"
           .=> iCase `(x) implicitFalse (showClauses [ti.name] Nothing ti)

  logMsg "derive.definitions" 1 $ show impl
  check $ var "mkShowPrec" .$ impl

||| Generate declarations and implementations for `Show` for a given data type.
export
Show : List Name -> ParamTypeInfo -> List TopLevel
Show nms p =
  [ TL (showClaim p) (showDef nms p.showName p.info)
  , TL (showImplClaim p) (showImplDef p)
  ]

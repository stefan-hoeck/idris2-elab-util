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
showClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
showClaim fun p =
  let arg := p.applied
      tpe := piAll `(Prec -> ~(arg) -> String) (allImplicits p "Show")
   in public' fun tpe

||| Top-level declaration of the `Show` implementation for the given data type.
export
showImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
showImplClaim impl p = implClaim impl (implType "Show" p)

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
  ttimp : BoundArg 1 Explicit -> TTImp
  ttimp (BA (MkArg M0 _ _ _) _   _) = primVal (Str " _")
  ttimp (BA (MkArg _  _ _ t) [x] _) = assertIfRec nms t `(showArg ~(var x))

  rsh : Name -> SnocList TTImp -> TTImp
  rsh n [<] = n.namePrim
  rsh n st  = `(conWithArgs p ~(n.namePrim) ~(listOf st))

  nttimp : BoundArg 1 NamedExplicit -> TTImp
  nttimp (BA a [x]   _) =
    let nm := (argName a).namePrim
     in case a.count of
       M0 => `(MkPair ~(nm) "_")
       _  =>
         let shown := assertIfRec nms a.type `(show ~(var x))
          in `(MkPair ~(nm) ~(shown))

  nrsh : Name -> SnocList TTImp -> TTImp
  nrsh n [<] = n.namePrim
  nrsh n st  = `(recordWithArgs p ~(n.namePrim) ~(listOf st))

  export
  showClauses : (fun : Maybe Name) -> TypeInfo -> List Clause
  showClauses fun ti = map clause ti.cons
    where clause : Con ti.arty ti.args -> Clause
          clause c =
            let ns  := freshNames "x" c.arty
                bc  := bindCon c ns
                lhs := maybe bc ((.$ pvar .$ bc) . var) fun
             in case all namedArg c.args of
                  True =>
                    let st := nttimp <$> boundArgs namedExplicit c.args [ns]
                     in lhs .= nrsh c.name st
                  False =>
                    let st := ttimp <$> boundArgs explicit c.args [ns]
                     in lhs .= rsh c.name st

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
  let fun  := funName p "showPrec"
      impl := implName p "Show"
   in [ TL (showClaim fun p) (showDef nms fun p.info)
      , TL (showImplClaim impl p) (showImplDef fun impl)
      ]

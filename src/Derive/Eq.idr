module Derive.Eq

import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Top-level declaration implementing the equality test for
||| the given data type.
export
eqClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
eqClaim fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg) -> Bool) (allImplicits p "Eq")
   in public' fun tpe

||| Top-level declaration implementing the `Eq` interface for
||| the given data type.
export
eqImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
eqImplClaim impl p = implClaim impl (implType "Eq" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

eqImplDef : (fun, impl : Name) -> Decl
eqImplDef fun impl = def impl [var impl .= var "mkEq" .$ var fun]

-- catch-all pattern clause for data types with more than
-- one data constructor
catchAll : (fun : Name) -> TypeInfo -> List Clause
catchAll fun ti =
  if length ti.cons > 1
     then [`(~(var fun) _ _) .= `(False)]
     else []

-- accumulate right-hand side of a single pattern clause
rhs : SnocList TTImp -> TTImp
rhs Lin       = `(True)
rhs (sx :< x) = foldr (\e,acc => `(~(e) && ~(acc))) x sx

parameters (nms : List Name)
  ttimp : BoundArg 2 Regular -> TTImp
  ttimp (BA arg [x,y] _) = assertIfRec nms arg.type `(~(var x) == ~(var y))

  ||| Generates pattern match clauses for the constructors of
  ||| the given data type. `fun` is the name of the function we implement.
  ||| This is either a local function definition in case of a
  ||| custom derivation, or the name of a top-level function.
  export
  eqClauses : (fun : Name) -> TypeInfo -> List Clause
  eqClauses fun ti = map clause ti.cons ++ catchAll fun ti
   where clause : Con ti.arty ti.args -> Clause
         clause c =
           let nx := freshNames "x" c.arty
               ny := freshNames "y" c.arty
               st := ttimp <$> boundArgs regular c.args [nx,ny]
            in var fun .$ bindCon c nx .$ bindCon c ny .= rhs st

  ||| Definition of a (local or top-level) function implementing
  ||| the equality check for the given data type.
  export
  eqDef : Name -> TypeInfo -> Decl
  eqDef fun ti = def fun (eqClauses fun ti)

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Derive an implementation of `Eq a` for a custom data type `a`.
|||
||| Note: This is mainly to be used for indexed data types. Consider using
|||       `derive` together with `Derive.Eq.Eq` for parameterized data types.
export %macro
deriveEq : Elab (Eq f)
deriveEq = do
  Just tpe <- goal
    | Nothing => fail "Can't infer goal"
  let Just (resTpe, nm) := extractResult tpe
    | Nothing => fail "Invalid goal type: \{show tpe}"
  ti <- getInfo' nm

  let impl :=  lambdaArg {a = Name} "x"
           .=> lambdaArg {a = Name} "y"
           .=> iCase `(MkPair x y) implicitFalse (eqClauses [ti.name] "MkPair" ti)

  logMsg "derive.definitions" 1 $ show impl
  check $ var "mkEq" .$ impl

||| Generate declarations and implementations for `Eq` for a given data type.
export
Eq : List Name -> ParamTypeInfo -> List TopLevel
Eq nms p =
  let fun  := funName p "eq"
      impl := implName p "Eq"
   in [ TL (eqClaim fun p) (eqDef nms fun p.info)
      , TL (eqImplClaim impl p) (eqImplDef fun impl)
      ]

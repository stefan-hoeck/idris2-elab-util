module Derive.Eq

import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Name of the top-level function implementing the derived equality test.
public export
(.eqName) : Named a => a -> Name
v.eqName = UN $ Basic "eq\{v.nameStr}"

||| General type of an equality test with the given list
||| of implicit and auto-implicit arguments, plus the given argument type
||| to be tested for equality.
export
generalEqType : (implicits : List Arg) -> (arg : TTImp) -> TTImp
generalEqType is arg = piAll `(~(arg) -> ~(arg) -> Bool) is

||| Implicit and auto-implicit arguments required to implement
||| an equality test for the given parameterized type.
export
eqImplicits : (p : ParamTypeInfo) -> PNames p -> List Arg
eqImplicits p ns = implicits ns ++ constraints p ns "Eq"

||| Type of the top-level function implementing the derived equality test.
export
eqType : (p : ParamTypeInfo) -> PNames p -> TTImp
eqType p ns = generalEqType (eqImplicits p ns) (applied p ns)

||| Top-level function declaration implementing the equality test for
||| the given data type.
export
eqClaim : (p : ParamTypeInfo) -> PNames p -> Decl
eqClaim p ns = public' p.eqName (eqType p ns)

||| Name of the derived interface implementation.
public export
(.eqImplName) : Named a => a -> Name
v.eqImplName = UN $ Basic "eqImpl\{v.nameStr}"

||| Type of the top-level function providing the `Eq` interface
||| for the given data type.
export
eqImplType : (p : ParamTypeInfo) -> PNames p -> TTImp
eqImplType p ns = piAll (var "Eq" .$ applied p ns) (eqImplicits p ns)

||| Top-level declaration implementing the `Eq` interface for
||| the given data type.
export
eqImplClaim : (p : ParamTypeInfo) -> PNames p -> Decl
eqImplClaim p ns = implClaim p.eqImplName (eqImplType p ns)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
eqImplDef : (p : ParamTypeInfo) -> Decl
eqImplDef p =
  def p.eqImplName [var p.eqImplName .= var "mkEq" .$ var p.eqName]

-- catch-all pattern clause for data types with more than
-- one data constructor
catchAll : (fun : Name) -> TypeInfo -> List Clause
catchAll fun ti =
  if length ti.cons > 1
     then [`(~(var fun) _ _) .= `(False)]
     else []

parameters (nms : List Name)
  -- Equality test for a set of constructor arguments.
  -- Checks if the argument types are safely recursive, that is, contains
  -- one of the data type names listed in `nms`. If so, prefixes
  -- the generated function call with `assert_total`.
  eqRHS : SnocList TTImp -> Vect n Arg -> Vect n Name -> Vect n Name -> TTImp
  eqRHS st (x :: xs) (y :: ys) (z :: zs) = case isExplicitUnerased x of
    True  =>
      let t := assertIfRec nms x.type `(~(var y) == ~(var z))
       in eqRHS (st :< t) xs ys zs
    False => eqRHS st xs ys zs
  eqRHS Lin       [] [] [] = `(True)
  eqRHS (sx :< x) [] [] [] = foldr (\e,acc => `(~(e) && ~(acc))) x sx

  ||| Generates pattern match clauses for the constructors of
  ||| the given data type. `fun` is the name of the function we implement.
  ||| This is either a local function definition in case of a
  ||| custom derivation, or the name of a top-level function.
  export
  eqClauses : (fun : Name) -> TypeInfo -> List Clause
  eqClauses fun ti = map clause ti.cons ++ catchAll fun ti
    where clause : Con ti.arty ti.args -> Clause
          clause c =
            let nx    := freshNames "x" c.arty
                ny    := freshNames "y" c.arty
             in var fun .$ bindCon c nx .$ bindCon c ny .=
                eqRHS Lin c.args nx ny

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
  let ns := freshNames "par" p.info.arty
   in [ TL (eqClaim p ns) (eqDef nms p.eqName p.info)
      , TL (eqImplClaim p ns) (eqImplDef p)
      ]

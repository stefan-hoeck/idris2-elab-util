module Derive.Ord

import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Constructor Index
--------------------------------------------------------------------------------

||| Type used to represent the index of a data constructor.
export
conIndexTypes : Nat -> (Bits32 -> TTImp, TTImp)
conIndexTypes n =
  let f := primVal . PrT
   in if      n < 256     then (primVal . B8 . cast, f Bits8Type)
      else if n < 0x20000 then (primVal . B16 . cast, f Bits16Type)
      else                     (primVal . B32, f Bits32Type)

||| Clauses returning the index for each constructor in the given
||| list.
export
conIndexClauses : Named a => Name -> List a -> List Clause
conIndexClauses n ns = go 0 (fst $ conIndexTypes $ length ns) ns
  where go : Bits32 -> (Bits32 -> TTImp) -> List a -> List Clause
        go _  _ []        = []
        go ix f (c :: cs) = (var n .$ bindAny c .= f ix) :: go (ix + 1) f cs

||| Name of the function returning the constructor index.
export
(.conIndexName) : Named a => a -> Name
v.conIndexName = UN $ Basic "conIndex\{v.nameStr}"

||| Declaration of a function returning the constructor index
||| for a value of the given data type.
export
conIndexClaim : (t : TypeInfo) -> Vect t.arty Name -> Decl
conIndexClaim t ns =
  let tpe := snd (conIndexTypes $ length t.cons)
      arg := appArgs t.name ns
   in public' t.conIndexName $ piAll `(~(arg) -> ~(tpe)) (implicits ns)

||| Definition of a function returning the constructor index
||| for a value of the given data type.
export
conIndexDef : TypeInfo -> Decl
conIndexDef t =
  let nm := t.conIndexName
   in def nm $ conIndexClauses nm t.cons

||| For the given data type, creates a function for returning
||| a 0-based index for each constructor.
|||
||| For instance, for `Either a b = Left a | Right b` this creates
||| declarations as follows:
|||
||| ```idris
||| conIndexEither : Either a b -> Bits8
||| conIndexEither (Left {})  = 0
||| conIndexEither (Right {}) = 1
||| ```
|||
||| This function is useful in several situations: When deriving
||| `Ord` for a sum type with more than one data constructors, we
||| can use the constructor index to compare values created from
||| distinct constructors. This allows us to only use a linear number
||| of pattern matches to implement the ordering.
|||
||| For enum types (all data constructors have only erased arguments - if any),
||| there are even greater benefits: `conIndex` is
||| the identity function at runtime, being completely eliminated during
||| code generations. This allows us to get `Eq` and `Ord` implementations for
||| enum types, which run in O(1)!
export
ConIndex : List Name -> TypeInfo -> List TopLevel
ConIndex _ t =
  let ns := freshNames "par" t.arty
   in [ TL (conIndexClaim t ns) (conIndexDef t) ]

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Name of the top-level function implementing the derived ordering test.
public export
(.ordName) : Named a => a -> Name
v.ordName = UN $ Basic "ord\{v.nameStr}"

||| Top-level function declaration implementing the ordering test for
||| the given data type.
export
ordClaim : (p : ParamTypeInfo) -> Decl
ordClaim p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg) -> Ordering) (allImplicits p "Ord")
   in public' p.ordName tpe

||| Name of the derived interface implementation.
public export
(.ordImplName) : Named a => a -> Name
v.ordImplName = UN $ Basic "ordImpl\{v.nameStr}"

||| Top-level declaration implementing the `Ord` interface for
||| the given data type.
export
ordImplClaim : (p : ParamTypeInfo) -> Decl
ordImplClaim p = implClaim p.ordImplName (implType "Ord" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
ordImplDef : ParamTypeInfo -> Decl
ordImplDef p =
  def p.ordImplName [var p.ordImplName .= var "mkOrd" .$ var p.ordName]

-- Generates the right-hand side of the ordering test on a single
-- pair of (identical) data constructors based on the given list of
-- comparisons.
ordRHS : List TTImp -> TTImp
ordRHS []        = `(EQ)
ordRHS (x :: []) = x
ordRHS (x :: xs) = `(case ~(x) of {EQ => ~(ordRHS xs); o => o})

-- catch-all pattern clause for data types with more than
-- one data constructor
catchAll : (fun : Name) -> TypeInfo -> List Clause
catchAll fun ti =
  let civ      := var ti.conIndexName
  in if length ti.cons > 1
       then [`(~(var fun) x y) .= `(compare (~(civ) x) (~(civ) y))]
       else []

parameters (nms : List Name)
  -- Ordering test for a set of constructor arguments.
  -- Checks if the argument types are safely recursive, that is, contains
  -- one of the data type names listed in `nms`. If so, prefixes
  -- the generated function call with `assert_total`.
  ordArgs : Vect n Arg -> Vect n Name -> Vect n Name -> List TTImp
  ordArgs []        []        []        = []
  ordArgs (x :: xs) (y :: ys) (z :: zs) = case isExplicitUnerased x of
    True  => assertIfRec nms x.type `(compare ~(var y) ~(var z)) :: ordArgs xs ys zs
    False => ordArgs xs ys zs

  ||| Generates pattern match clauses for the constructors of
  ||| the given data type. `fun` is the name of the function we implement.
  ||| This is either a local function definition in case of a
  ||| custom derivation, or the name of a top-level function.
  export
  ordClauses : (fun : Name) -> (t : TypeInfo) -> List Clause
  ordClauses fun ti = map clause ti.cons ++ catchAll fun ti
    where clause : Con ti.arty ti.args -> Clause
          clause c =
            let nx := freshNames "x" c.arty
                ny := freshNames "y" c.arty
             in var fun .$ bindCon c nx .$ bindCon c ny .=
                ordRHS (ordArgs c.args nx ny)

  ||| Definition of a (local or top-level) function implementing
  ||| the ordering check for the given data type.
  export
  ordDef : Name -> TypeInfo -> Decl
  ordDef fun ti = def fun (ordClauses fun ti)

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Derive an implementation of `Ord a` for a custom data type `a`.
|||
||| Note: This is mainly to be used for indexed data types. Consider using
|||       `derive` together with `Derive.Ord.Ord` for parameterized data types.
export %macro
deriveOrd : Elab (Ord f)
deriveOrd = do
  Just tpe <- goal
    | Nothing => fail "Can't infer goal"
  let Just (resTpe, nm) := extractResult tpe
    | Nothing => fail "Invalid goal type: \{show tpe}"
  ti <- getInfo' nm

  let impl :=  lambdaArg {a = Name} "x"
           .=> lambdaArg {a = Name} "y"
           .=> iCase `(MkPair x y) implicitFalse (ordClauses [ti.name] "MkPair" ti)

  logMsg "derive.definitions" 1 $ show impl
  check $ var "mkOrd" .$ impl

||| Generate declarations and implementations for `Ord` for a given data type.
export
Ord : List Name -> ParamTypeInfo -> List TopLevel
Ord nms p =
  let pre := if length p.cons > 1 then ConIndex nms p.info else []
   in pre ++
      [ TL (ordClaim p) (ordDef nms p.ordName p.info)
      , TL (ordImplClaim p) (ordImplDef p)
      ]

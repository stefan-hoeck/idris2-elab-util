module Derive.Eq

import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Constructor Index
--------------------------------------------------------------------------------

export
conIndexName : Named a => a -> Name
conIndexName v = funName v "conIndex"

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

||| Declaration of a function returning the constructor index
||| for a value of the given data type.
export
conIndexClaim : (fun : Name) -> (t : TypeInfo) -> Decl
conIndexClaim fun t =
  let tpe := snd (conIndexTypes $ length t.cons)
      arg := t.applied
   in public' fun $ piAll `(~(arg) -> ~(tpe)) (t.implicits)

||| Definition of a function returning the constructor index
||| for a value of the given data type.
export
conIndexDef : (fun : Name) -> TypeInfo -> Decl
conIndexDef fun t = def fun $ conIndexClauses fun t.cons

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
ConIndex : List Name -> ParamTypeInfo -> Res (List TopLevel)
ConIndex _ t =
  let fun := conIndexName t
   in Right [ TL (conIndexClaim fun t.info) (conIndexDef fun t.info) ]

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

eqEnumDef : (impl, ci : Name) -> Decl
eqEnumDef i c = def i [var i .= `(mkEq $ \x,y => ~(var c) x == ~(var c) y)]

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
  arg : BoundArg 2 Regular -> TTImp
  arg (BA g [x,y] _) = assertIfRec nms g.type `(~(varStr x) == ~(varStr y))

  ||| Generates pattern match clauses for the constructors of
  ||| the given data type. `fun` is the name of the function we implement.
  ||| This is either a local function definition in case of a
  ||| custom derivation, or the name of a top-level function.
  export
  eqClauses : (fun : Name) -> TypeInfo -> List Clause
  eqClauses fun ti = map clause ti.cons ++ catchAll fun ti
   where
     clause : Con ti.arty ti.args -> Clause
     clause = accumArgs2 regular (\x,y => var fun .$ x .$ y) rhs arg

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
Eq : List Name -> ParamTypeInfo -> Res (List TopLevel)
Eq nms p = case isEnum p.info of
  True  =>
    let impl := implName p "Eq"
        ci   := conIndexName p
     in sequenceJoin
          [ConIndex nms p, Right [ TL (eqImplClaim impl p) (eqEnumDef impl ci) ]]
  False =>
    let fun  := funName p "eq"
        impl := implName p "Eq"
     in Right [ TL (eqClaim fun p) (eqDef nms fun p.info)
              , TL (eqImplClaim impl p) (eqImplDef fun impl)
              ]

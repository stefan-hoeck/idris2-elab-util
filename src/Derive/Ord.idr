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

||| Declaration of a function returning the constructor index
||| for a value of the given data type.
export
conIndexClaim : (fun : Name) -> (t : TypeInfo) -> Vect t.arty Name -> Decl
conIndexClaim fun t ns =
  let tpe := snd (conIndexTypes $ length t.cons)
      arg := appArgs t.name ns
   in public' fun $ piAll `(~(arg) -> ~(tpe)) (implicits ns)

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
ConIndex : List Name -> TypeInfo -> List TopLevel
ConIndex _ t =
  let ns  := freshNames "par" t.arty
      fun := funName t "conIndex"
   in [ TL (conIndexClaim fun t ns) (conIndexDef fun t) ]

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Top-level function declaration implementing the ordering test for
||| the given data type.
export
ordClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
ordClaim fun p =
  let arg := p.applied
      tpe := piAll `(~(arg) -> ~(arg) -> Ordering) (allImplicits p "Ord")
   in public' fun tpe

||| Top-level declaration implementing the `Ord` interface for
||| the given data type.
export
ordImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
ordImplClaim impl p = implClaim impl (implType "Ord" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
ordImplDef : (fun, impl : Name) -> Decl
ordImplDef fun impl = def impl [var impl .= var "mkOrd" .$ var fun]

-- Generates the right-hand side of the ordering test on a single
-- pair of (identical) data constructors based on the given list of
-- comparisons.
rhs : SnocList TTImp -> TTImp
rhs [<]       = `(EQ)
rhs (sx :< x) = foldr (\e,acc => `(case ~(e) of {EQ => ~(acc); o => o})) x sx

-- catch-all pattern clause for data types with more than
-- one data constructor
catchAll : (ci : Name) -> (fun : Name) -> TypeInfo -> List Clause
catchAll ci fun ti =
  let civ      := var ci
  in if length ti.cons > 1
       then [`(~(var fun) x y) .= `(compare (~(civ) x) (~(civ) y))]
       else []

parameters (nms : List Name)
  ttimp : BoundArg 2 UnerasedExplicit -> TTImp
  ttimp (BA arg [x,y] _) = assertIfRec nms arg.type `(compare ~(var x) ~(var y))

  ||| Generates pattern match clauses for the constructors of
  ||| the given data type. `fun` is the name of the function we implement.
  ||| This is either a local function definition in case of a
  ||| custom derivation, or the name of a top-level function.
  export
  ordClauses : (ci, fun : Name) -> (t : TypeInfo) -> List Clause
  ordClauses ci fun ti = map clause ti.cons ++ catchAll ci fun ti
    where clause : Con ti.arty ti.args -> Clause
          clause c =
            let nx := freshNames "x" c.arty
                ny := freshNames "y" c.arty
                st := ttimp <$> boundArgs unerasedExplicit c.args [nx,ny]
             in var fun .$ bindCon c nx .$ bindCon c ny .= rhs st

  ||| Definition of a (local or top-level) function implementing
  ||| the ordering check for the given data type.
  export
  ordDef : (ci, fun : Name) -> TypeInfo -> Decl
  ordDef ci fun ti = def fun (ordClauses ci fun ti)

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Ord` for a given data type.
export
Ord : List Name -> ParamTypeInfo -> List TopLevel
Ord nms p =
  let ci   := funName p "conIndex"
      pre  := if length p.cons > 1 then ConIndex nms p.info else []
      fun  := funName p "ord"
      impl := implName p "Ord"
   in pre ++
      [ TL (ordClaim fun p) (ordDef nms ci fun p.info)
      , TL (ordImplClaim impl p) (ordImplDef fun impl)
      ]

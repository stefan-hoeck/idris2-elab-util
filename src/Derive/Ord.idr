module Derive.Ord

import public Derive.Eq

%default total

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

ordEnumDef : (impl, ci : Name) -> Decl
ordEnumDef i c =
  def i [var i .= `(mkOrd $ \x,y => compare (~(var c) x) (~(var c) y))]

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
  arg : BoundArg 2 Regular -> TTImp
  arg (BA g [x,y] _) = assertIfRec nms g.type `(compare ~(varStr x) ~(varStr y))

  ||| Generates pattern match clauses for the constructors of
  ||| the given data type. `fun` is the name of the function we implement.
  ||| This is either a local function definition in case of a
  ||| custom derivation, or the name of a top-level function.
  export
  ordClauses : (ci, fun : Name) -> (t : TypeInfo) -> List Clause
  ordClauses ci fun ti = map clause ti.cons ++ catchAll ci fun ti
   where
     clause : Con ti.arty ti.args -> Clause
     clause = accumArgs2 regular (\x,y => var fun .$ x .$ y) rhs arg

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
Ord : List Name -> ParamTypeInfo -> Res (List TopLevel)
Ord nms p = case isEnum p.info of
  True  =>
    let impl := implName p "Ord"
        ci   := conIndexName p
     in Right [ TL (ordImplClaim impl p) (ordEnumDef impl ci) ]
  False =>
    let ci   := conIndexName p
        pre  := if length p.cons > 1 then ConIndex nms p else Right []
        fun  := funName p "ord"
        impl := implName p "Ord"
     in sequenceJoin
          [ pre
          , Right [ TL (ordClaim fun p) (ordDef nms ci fun p.info)
                  , TL (ordImplClaim impl p) (ordImplDef fun impl)
                  ]
          ]

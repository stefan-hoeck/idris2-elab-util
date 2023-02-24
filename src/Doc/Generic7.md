# Verified Interfaces Part 2

With all the preparations from [part 1](Generic6.md) behind us,
we will derive provably correct implementations for `Eq`
automatically.

```idris
module Doc.Generic7

import Doc.Generic6

import Data.Vect.Quantifiers
import Language.Reflection.Util

%language ElabReflection
```

## A lawful version of `Generic`

First, we should make sure that implementations of `Generic`
themselves are well behaved. We expect that a data type
and its generic representation are isomorphic and not
a single piece of information is lost when going from one
to the other and back. Thus, the following two laws must hold:
`from . to = id` and `to . from = id`.

```idris
||| Identity for types
public export
I : Type -> Type
I = id

public export
interface Generic (0 t : Type) (0 code : List $ List Type) | t where
  ||| Converts the data type to its generic representation.
  total from : (v : t) -> SOP I code

  ||| Converts the generic representation back to the original
  ||| value.
  total to   : (v : SOP I code) -> t

  ||| Proof that `to . from = id`.
  total fromToId : (v : t) -> to (from v) = v

  ||| Proof that `from . to = id`.
  total toFromId : (v : SOP I code) -> from (to v) = v
```

Let's just quickly write an implementation for `Maybe` to
see how this has to be done:

```idris
public export
Generic (Maybe a) [[],[a]] where
  from Nothing  = Z []
  from (Just v) = S $ Z [v]

  to (Z [])      = Nothing
  to (S $ Z [v]) = Just v

  fromToId Nothing  = Refl
  fromToId (Just v) = Refl

  toFromId (Z [])      = Refl
  toFromId (S $ Z [v]) = Refl
```

So the additional proofs are almost exactly a repetition
of the actual implementations. This should be very easy to
do using elaborator reflection:

```idris
private
ConNames : Type
ConNames = (Name, List String, List TTImp)

export
mkGeneric : Name
mkGeneric = singleCon "Generic"

private
mkSOP1 : (k : Nat) -> (arg : TTImp) -> TTImp
mkSOP1 0     arg = `(Z ~(arg))
mkSOP1 (S k) arg = `(S ~(mkSOP1 k arg))

mkSOP : Foldable t => (k : Nat) -> (args : t TTImp) -> TTImp
mkSOP k = mkSOP1 k . listOf

||| Creates the syntax tree for the code of the given data type.
||| We export this since it might be useful elsewhere.
export
mkCode : (p : ParamTypeInfo) -> TTImp
mkCode p = listOf $ map (\c => listOf $ explicits c.args) p.cons
  where explicits : Vect n (ConArg p.numParams) -> List TTImp
        explicits [] = []
        explicits (CArg _ _ ExplicitArg t :: as) =
          ttimp p.paramNames t :: explicits as
        explicits (_ :: as) = explicits as

private
fromClause : (Nat,ConNames) -> Clause
fromClause (k,(con,ns,vars)) = patClause (bindAll con ns) (mkSOP k vars)

private
fromToIdClause : (Nat,ConNames) -> Clause
fromToIdClause (k,(con,ns,vars)) = patClause (bindAll con ns) `(Refl)

private
toClause : (Nat,ConNames) -> Clause
toClause (k,(con,ns,vars)) =
  patClause (mkSOP k $ map bindVar ns) (appAll con vars)

private
toFromIdClause : (Nat,ConNames) -> Clause
toFromIdClause (k,(con,ns,vars)) = patClause (mkSOP k $ map bindVar ns) `(Refl)

private
zipWithIndex : List a -> List (Nat,a)
zipWithIndex as = run 0 as
  where run : Nat -> List a -> List (Nat,a)
        run _ []     = []
        run k (h::t) = (k,h) :: run (S k) t

conNames : ParamCon n -> ConNames
conNames c =
  let ns   := toList $ freshNames "x" (count isExplicit c.args)
      vars := map varStr ns
   in (c.name, ns, vars)

||| Derives a `Generic` implementation for the given data type
||| and visibility.
export
GenericVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
GenericVis vis _ p =
  let names    = zipWithIndex (map conNames p.cons)
      fun      = UN . Basic $ "implGeneric" ++ camelCase p.info.name

      appType  = p.applied
      genType  = `(Generic ~(appType) ~(mkCode p))
      funType  = piAll genType p.implicits

      x        = lambdaArg {a = Name} "x"
      varX     = var "x"
      from     = lam x $ iCase varX implicitFalse (map fromClause names)
      to       = lam x $ iCase varX implicitFalse (map toClause names)
      fromToId = lam x $ iCase varX implicitFalse (map fromToIdClause names)
      toFromId = lam x $ iCase varX implicitFalse (map toFromIdClause names)

      impl     = appAll mkGeneric [from,to,fromToId,toFromId]

   in Right
        [ TL (interfaceHint vis fun funType)
             (def fun [patClause (var fun) impl])]

||| Alias for `GenericVis Public`.
export
Generic' : List Name -> ParamTypeInfo -> Res (List TopLevel)
Generic' = GenericVis Public
```

We have seen most of this before. The only new parts are
the clauses and implementations for `fromToId` and `toFromId`, both
of which are mostly identical to `toId` and `fromId`.

## Generic Equality

As before, we can implement `genEq`.

```idris
||| Default `(==)` implementation for data types with a `Generic`
||| instance.
public export %inline
genEq : Generic t code => Eq (SOP I code) => t -> t -> Bool
genEq x y = from x == from y
```

Proving laws about `genEq` is straight forward, since we
already know the laws hold for the `Eq` instance of `SOP`:

```idris
export total
genEqRefl :  Generic t code => EqV (SOP I code)
          => (x : t) -> genEq x x = True
genEqRefl x with (from x)
  genEqRefl x | gx = eqRefl gx

export total
genEqSym :  Generic t code => EqV (SOP I code)
         => (x,y : t) -> genEq x y = genEq y x
genEqSym x y with (from x)
  genEqSym x y | gx with (from y)
    genEqSym x y | gx | gy = eqSym gx gy

export total
genEqTrans :  Generic t code => EqV (SOP I code)
           => (x,y,z : t)
           -> genEq x y = True
           -> genEq y z = True
           -> genEq x z = True
genEqTrans x y z xy yz with (from x)
  genEqTrans x y z xy yz | gx with (from y)
    genEqTrans x y z xy yz | gx | gy with (from z)
      genEqTrans x y z xy yz | gx | gy | gz = eqTrans gx gy gz xy yz
```

With this we are able to trivially implement `EqV` for
generically derived instances of `Eq`:

```idris
data TestSum  = A Int String
              | B Bool
              | C String

%runElab derive "TestSum" [Generic']

Eq TestSum where (==) = genEq

EqV TestSum where
  eqRefl       = genEqRefl
  eqSym        = genEqSym
  eqTrans      = genEqTrans
  neqNotEq _ _ = Refl
```

And thus, we can derive provably lawful instances of `Eq`
automatically from a data type's generic representation:

```idris
mkEqV :  Eq a
      => (eqRefl   : (x : a) -> IsEq x x)
      -> (eqSym    : (x,y : a) -> (x == y) = (y == x))
      -> (eqTrans  : (x,y,z : a) -> IsEq x y -> IsEq y z -> IsEq x z)
      -> (neqNotEq : (x,y : a) -> (x /= y) = not (x == y))
      -> EqV a
mkEqV = %runElab check (var $ singleCon "EqV")

Eq' : List Name -> ParamTypeInfo -> Res (List TopLevel)
Eq' _ p =
  let nm := implName p "Eq"
      cl := patClause (var nm) `(mkEq genEq)
   in Right [TL (implClaim nm (implType "Eq" p)) (def nm [cl])]

EqV' : List Name -> ParamTypeInfo -> Res (List TopLevel)
EqV' _ p =
  let nm := implName p "EqV"
      cl := patClause (var nm) `(mkEqV genEqRefl genEqSym genEqTrans (\_,_ => Refl))
   in Right [TL (implClaim nm (implType "EqV" p)) (def nm [cl])]

data AnotherSum : Type where
  Var   : (v : String) -> AnotherSum
  Op    : (x : Int)    -> AnotherSum
  Empty : AnotherSum

%runElab derive "AnotherSum" [Generic', Eq', EqV']
```

## Limitations

Quite a few of the limitations listed here in earlier
versions of this post could be resolved by now. I'll
leave the following two notes as references for
potential changes / challenges in the future:

Concerning provably correct interface implementations,
there is [issue #72](https://github.com/idris-lang/Idris2/issues/72),
leading to problems with diamond shaped inheritance structures.
This was not a problem with `EqV` but it might well become
a problem once we start writing an `OrdV` instance
and try to put this in relation with `EqV`.

In addition, there is [another proposal](https://github.com/idris-lang/Idris2/issues/777)
for writing correctness proofs for interface implementations.
With this, we'd not have to write additional interface
hierarchies.

## What's next

I consider the part about generics to be mostly finished for the time
being. Yet, there are some things still to be addressed: Support
for generic derivation of indexed types and existentials might be
of interest. Also the derivation of 'higher-kinded' interface
implementations like for `Functor` and `Traversable` is not
yet possible. Of course I will write about these things if
I find working solutions.

There will of course also be other use cases for elaborator
reflection. I'm looking forward to learning something about
using the technique for proof searching, for instance.
Interesting results will be posted here, promise. :-)

<!-- vi: filetype=idris2:syntax=markdown
-->

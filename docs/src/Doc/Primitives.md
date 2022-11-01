# Refined Primitives

The other day I came upon a nice and simple use case for some
very straightforward elaborator reflection to avoid
writing boring boilerplate code. I thought others might find
this useful as well, so here we go.

```idris
module Doc.Primitives

import Data.Maybe
import Data.So
import Language.Reflection.Derive

%language ElabReflection

%default total
```

## Primitive Wrapper Types

In real world applications, it is often necessary to write
wrapper types for (refined) primitives, either out of
performance considerations or when writing a full fledged
algebraic data type is just not worth the hassle.
As an example, in cheminformatics we probably want to define
a type for atomic numbers. These represent the number of
protons in the nuclei of atoms and are in a one to one relation
with the known chemical elements. Since there are - as of today -
118 known elements, atomic numbers should be integers in the
range 1 to 118.

In a language like Haskell, we'd probably use an abstract
newtype wrapper for this:

```haskell
newtype AtomicNr = AtomicNr { unAtomicNr :: Int }
  deriving (Show, Eq, Ord)

atomicNr :: Int -> Maybe AtomicNr
atomicNr n | 1 <= n && n <= 118 = Just $ AtomicNr n
           | otherwise          = Nothing
```

While this would be safe and give us
the necessary runtime guarantees, it would be rather inconvenient
to use at compile time, where we'd have to either provide
an unchecked constructor or deal with that cumbersome
`Maybe` return type.

In Idris, we can do much better:

```idris
record AtomicNr where
  constructor MkAtomicNr
  value      : Int
  0 inBounds : So (1 <= value && value <= 118)
```

Here, the proof of validity is builtin, which
allows us to publicly export `AtomicNr` without
fear of invalid values being wrapped up in client code:

```idris
fluorine : AtomicNr
fluorine = MkAtomicNr 19 Oh
```

Some standard interface implementations come almost for free:

```idris
Eq AtomicNr where
  (==) = (==) `on` value

Ord AtomicNr where
  compare = compare `on` value

Show AtomicNr where
  showPrec p = showPrec p . value
```

In order to create values of `AtomicNr` at runtime as well
as at compile time, we provide two utility functions. Since these will
have the same names for other refined primitives (in case of
`fromInteger`, this is out of necessity), we put them in their own namespace:

```idris
-- this is necessary since Data.So.choose is not exported
-- publicly and will therefore not reduce during unification.
maybeSo : (b : Bool) -> Maybe (So b)
maybeSo True  = Just Oh
maybeSo False = Nothing

refineSo :  {f : a -> Bool}
         -> (make : (v : a) -> (0 prf : So $ f v) -> b)
         -> (val : a)
         -> Maybe b
refineSo make val = case maybeSo (f val) of
                         Just oh => Just $ make val oh
                         Nothing => Nothing

namespace AtomicNr
  refine : Int -> Maybe AtomicNr
  refine = refineSo MkAtomicNr

  fromInteger :  (v : Integer)
              -> {auto 0 _: IsJust (refine $ fromInteger v)}
              -> AtomicNr
  fromInteger v = fromJust (refine $ fromInteger v)
```

Let's see, whether this works:

```idris
hydrogen : AtomicNr
hydrogen = 1

oganesson : AtomicNr
oganesson = 118
```

Neat. But of course, almost all the code we wrote above is completely
uninteresting and would look almost exactly the same for other
refined wrappers. This calls for metaprogramming, doesn't it?

## Using Elaborator Reflection to cut the Boilerplate

Before we start implementing a very simple elaborator script,
we first agree on certain conventions, which will make the elaborator
script much simpler:

* A refined primitive is a record consisting of a wrapped value and an
  erased `So`, which proves the validity of the wrapped value.
* If the refined primitive has name `Foo`, its constructor is named
  `MkFoo`.
* The accessor for the wrapped field is named `value`.

This allows us to generate the necessary declarations without much
hassle. First, we generate declarations for the interface implementations.
We can use functions `mkEq`, `mkOrd`, and `mkShow`
from `Language.Reflection.Derive` and some utilities from
`Language.Reflection.Syntax` here. The implementations themselves
are just quoted versions of what we wrote above:

```idris
export covering
refinedEqOrdShow : String -> List Decl
refinedEqOrdShow n =
  let eqFun   = UN . Basic $ "implEq"   ++ n
      ordFun  = UN . Basic $ "implOrd"  ++ n
      showFun = UN . Basic $ "implShow" ++ n

      tpe     = varStr n

   in [ interfaceHint Public eqFun `(Eq ~(tpe))
      , def eqFun [patClause (var eqFun) `(mkEq ((==) `on` value))]
      , interfaceHint Public ordFun `(Ord ~(tpe))
      , def ordFun [patClause (var ordFun) `(mkOrd (compare `on` value))]
      , interfaceHint Public showFun `(Show ~(tpe))
      , def showFun [patClause (var showFun)
                     `(mkShowPrec (\p => showPrec p . value))]
      ]
```

Coming up with the conversion functions `refine` and `fromInteger`
is even simpler, since we can quote the whole block almost literally.
Only for the type and constructor names we will have to use unquotes:

```idris
export covering
refinedInt : String -> Elab ()
refinedInt n =
  let con  = varStr $ "Mk" ++ n
      ns   = MkNS [n]

      -- this has to be namespaced
      -- to avoid disambiguities when being used
      -- in fromInteger
      refineNS = var $ NS ns (UN $ Basic "refine")

   in declare $ refinedEqOrdShow n ++
        [ INamespace EmptyFC ns
          `[ public export
             refine : Int -> Maybe ~(varStr n)
             refine = refineSo ~(con)

             public export
             fromInteger :  (n : Integer)
                         -> {auto 0 _: IsJust (~(refineNS) $ fromInteger n)}
                         -> ~(varStr n)
             fromInteger n = fromJust (refine $ fromInteger n)
           ]
        ]
```

Let's give it a spin:

```idris
record MassNr where
  constructor MkMassNr
  value      : Int
  0 inBounds : So (1 <= value && value <= 511)

%runElab refinedInt "MassNr"

record Isotope where
  constructor MkIsotope
  atomicNr : AtomicNr
  massNr   : MassNr

c14 : Isotope
c14 = MkIsotope 6 14
```

## Conclusion

This concludes this tutorial post. As can be seen, if we know the structure
of data types in advance coming up with simple elaborator
scripts is very easy. The syntax to do so is lightweight,
especially in cases where we can quote most of the code directly.

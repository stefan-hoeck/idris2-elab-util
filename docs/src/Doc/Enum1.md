# A First Metaprogram: Defining Enumerations

This tutorial is set up as a literate Idris file. We
therefore need some module noise to get started.

```idris
module Doc.Enum1

import Language.Reflection
import Language.Reflection.Syntax

%language ElabReflection
```

## Enums

We often use sum types like `Weekday` below to define
well-typed choices of constant values.

```idris
data Weekday = Monday
             | Tuesday
             | Wednesday
             | Thursday
             | Friday
             | Saturday
             | Sunday
```

We will now write a metaprogram that generates similar
structures from a list of strings.

## First Implementation

```idris
enumDecl1 : (name : String) -> (cons : List String) -> Decl
```

Before we can implement `enumDecl`, we will inspect the
structure of a typical enum type at the REPL:

```repl
...> :exec putPretty `[data Enum = A | B | C]

  [ IData Private
          (MkData Enum
                  IType
                  []
                  [ MkTy A (IVar Enum)
                  , MkTy B (IVar Enum)
                  , MkTy C (IVar Enum) ]) ]

```

This leads to the following implementation:

```idris
enumDecl1 name cons = IData EmptyFC Public Nothing dat
  where enumName : Name
        enumName = UN $ Basic name

        mkCon : String -> ITy
        mkCon n = MkTy EmptyFC EmptyFC (UN $ Basic n) (IVar EmptyFC enumName)

        dat : Data
        dat = MkData EmptyFC enumName (IType EmptyFC) [] (map mkCon cons)
```

## Second Implementation

While it is typical for hand-written metaprograms to be
quite verbose, this library provides a selection of
utility functions for making the code above a bit more
concise. Module `Language.Reflection.Syntax` provides utility
aliases for many data constructors from `Language.Reflection.TTImp`
that allow us to drop the redundant passing of `EmptyFC`
constants. In addition, it comes with infix operators
similar to the ones shown in the pretty printer for
defining function application, type declarations and
anonymous functions. Finally, a handy `FromString`
instance for `Name` is provided, which determins from
the string passed whether the name is fully qualified or not.

```idris
export
enumDecl : (name : String) -> (cons : List String) -> Decl
enumDecl name = simpleData Public (UN $ Basic name) . map mkCon
  where mkCon : String -> ITy
        mkCon n = mkTy (UN $ Basic n) (varStr name)
```

Here, we used functions `simpleData`, `mkTy`, and `varStr`
from `Language.Reflection.Syntax`.

## Generating Enum Definitions

In order to use `enumDecl` to define an actual enum type,
we need function `declare` from `Language.Reflection`:

```idris
export
mkEnum : (name : String) -> (cons : List String) -> Elab ()
mkEnum name cons = declare [enumDecl name cons]
```

We can now tell Idris to generate an enum from
a data name and a list of constructor names for us:

```idris
%runElab mkEnum "Gender" ["Female","Male","NonBinary"]
```

The line above tells Idris to run the elaborator script
(`%runElab`) returned from the call to `mkEnum`. This
results in a new data type called `Gender` with nullary
data constructors `Female`, `Male`, and `NonBinary`
being defined. We should now have access to this new data
type. In order to test this, we implement an `Eq` instance
for it:

```idris
export
Eq Gender where
  Female     == Female     = True
  Male       == Male       = True
  NonBinary  == NonBinary  = True
  _          == _          = False
```

It worked! When we typecheck this file, Idris knows about
data type `Gender` and will accept our `Eq` implementation.
Note, that we needed to enable `%language ElabReflection` to
get access to `%runElab`.

## What's next

We have not gained much in terms of saved code from our
first metaprogram. However, the implementation of `Eq Gender`
above quickly identifies the next opportunity: Implementing
type class instances automatically. In the [next section](Enum2.md)
we'll give this a try.

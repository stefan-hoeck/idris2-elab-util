## A First Metaprogram: Defining Enumerations

This tutorial is set up as a literate Idris file. We
therefore need some module noise to get started.

```idris
module Doc.Enum1

import Language.Reflection
import Language.Reflection.Syntax

%language ElabReflection
```

### Enums

We often use sum types like `Weekday` below to define
well-typed choices of constant values.

```idris
public export
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

### First Implementation

```idris
enumDecl1 : (name : String) -> (cons : List String) -> Decl
```

Before we can implement `enumDecl`, we will inspect the
structure of a typical enum type at the REPL:

```
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
enumDecl1 name cons = IData EmptyFC Public dat
  where enumName : Name
        enumName = UN name

        mkCon : String -> ITy
        mkCon n = MkTy EmptyFC (UN n) (IVar EmptyFC enumName)

        dat : Data
        dat = MkData EmptyFC enumName (IType EmptyFC) [] (map mkCon cons)
```

### Second Implementation

While it is typical for hand-written metaprograms to be
quite verbose, this library provides a selection of
utility functions for making the code above a bit more
concise. Module `Language.Reflection.Syntax` provides utility
aliases for many data constructors from `Language.Reflection.TTImp`
that allow us to drop the reduntant passing of `EmptyFC`
constants. In addition, it comes with infix operators
similar to the ones shown in the pretty printer for
defining function application, type declarations and
anonymous functions. Finally, a handy `FromString`
instance for `Name` is provided, which determins from
the string passed whether the name is fully qualified or not.

```idris
enumDecl : (name : String) -> (cons : List String) -> Decl
enumDecl name = publicSimpleData (UN name) . map mkCon
  where mkCon : String -> ITy
        mkCon n = mkTy (UN n) (varStr name)
```

### Generating Enum Definitions

In order to us `enumDecl` to define an actual enum type,
we need function `declare` from `Language.Reflection`:

```idris
export
mkEnum : (name : String) -> (cons : List String) -> Elab ()
mkEnum name cons = declare [enumDecl name cons]
```

Lets try it:

```idris
%runElab (mkEnum "Gender" ["Female","Male","NonBinary"])

export
Eq Gender where
  Female     == Female     = True
  Male       == Male       = True
  NonBinary  == NonBinary  = True
  _          == _          = False
```

It worked! We need to enable `%language ElabReflection` to
get access to `%runElab`.

### What's next

We have not gained much in terms saved code from our
first metaprogram. However, the implementation of `Eq Gender`
above quickly identifies the next opportunity: Implementing
type class instances automatically. In the next section
we'll give this a try.

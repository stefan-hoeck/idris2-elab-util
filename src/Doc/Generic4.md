# Generic Deriving of Interface Implementations

We would now like to clean up the syntax for deriving
generic instances a bit. There is quite a bit of redundant
work going on, so we have the chance to reduce some code
duplication.

```idris
module Doc.Generic4

import public Language.Reflection.Pretty
import public Language.Reflection.Syntax
import public Language.Reflection.Types
import Doc.Generic1
import Doc.Generic3

%language ElabReflection
```

Note: Some of the types and utility functions described
here have been added to module `Language.Reflection.Derive`.

## An Intermediary Utility Type for Generic Deriving

First, we write a utility data type holding a top-level claim and
definition:

```idris
public export
record TopLevel where
  constructor TL
  claim : Decl
  defn  : Decl
```

We'd like to derive top-level definitions from some kind
of data object describing in detail the data type we are
interested in. Different representations are possible
(at the moment, we have seen `TypeInfo` and `ParamTypeInfo`),
so we want to abstract over the type providing the necessary
information:

```idris
public export
interface Named a => Elaborateable a where
  find_ : Elaboration m => Name -> m a

public export %inline
find : (0 a : Type) -> Elaborateable a => Elaboration m => Name -> m a
find _ = find_

export %inline
Elaborateable TypeInfo where
  find_ = getInfo'

export %inline
Elaborateable ParamTypeInfo where
  find_ = getParamInfo'
```

From these, we can come up with a first utility for deriving
all kinds of definitions:

```idris
derive1 :
     Elaboration m
  => Elaborateable t
  => Name
  -> List (t -> TopLevel)
  -> m ()
derive1 ns fs = do
  pt <- find t ns
  let name   := pt.getName
      tls    := map ($ pt) fs
      claims := map claim tls
      defns  := map defn tls

  declare $ claims ++ defns
```

## Instances for `Generic`, `Eq`, and `Ord`

We can now write `MkImplementation` values for `Generic`,
cleaning up parts of our code while we're at it.

```idris
implName : Named a => a -> (iface : String) -> Name
implName v iface = UN . Basic $ "impl" ++ iface ++ camelCase v.getName

private
conNames : ParamCon n -> ConNames
conNames c =
  let ns   := toList $ freshNames "x" (count isExplicit c.args)
      vars := map var ns
   in (c.name, map nameStr ns, vars)

export
Generic' : ParamTypeInfo -> TopLevel
Generic' p =
  let names    = zipWithIndex (map conNames p.cons)
      function = implName p "Generic"

      appType  = p.applied
      genType  = `(Generic) .$ appType .$ mkCode p
      funType  = piAll genType p.implicits

      x       = lambdaArg {a = Name} "x"
      varX    = var "x"
      from    = x .=> iCase varX implicitFalse (map fromClause names)
      to      = x .=> iCase varX implicitFalse (toClauses names)
      impl    = appAll "MkGeneric" [from,to]

   in TL (interfaceHint Public function funType)
         (def function [var function .= impl])

```

Before we can define the functions implementing `Eq`
and `Ord`, we must be able to prefix instance
declarations with the required implicit and auto implicit arguments.
For instance, the `Eq` instance of `Maybe` has the following type:

```repl
{0 a: _} -> Eq a => Eq (Maybe a)
```

`ParamTypeInfo` already provides this functionality, and we can make
use of it via the following utility function:

```idris
export
implementationType : (iface : Name) -> ParamTypeInfo -> TTImp
implementationType iface p =
  let appIface = var iface .$ p.applied
   in piAll appIface (allImplicits p iface)
```

We can now derive `Eq` implementation for data types with
a `Generic` implementation:

```idris
private
mkEq : TTImp
mkEq = `(MkEq genEq (\a,b => not (a == b)))

export
Eq' : ParamTypeInfo -> TopLevel
Eq' p =
  let function := implName p "Eq"
   in TL (interfaceHint Public function $ implementationType "Eq" p)
         (def function [var function .= mkEq])
```

Same for `Ord`:

```idris
private
mkOrd : TTImp
mkOrd =
  `(MkOrd
     genCompare
     (\a,b => compare a b == LT)
     (\a,b => compare a b == GT)
     (\a,b => compare a b /= GT)
     (\a,b => compare a b /= LT)
     (\a,b => if compare a b == GT then a else b)
     (\a,b => if compare a b == LT then a else b))

export
Ord' : ParamTypeInfo -> TopLevel
Ord' p =
  let function := implName p "Ord"
   in TL (interfaceHint Public function $ implementationType "Ord" p)
         (def function [var function .= mkOrd])
```

## Interface Implementations for `TTImp` and Friends

Finally, lets put our new utilities to work. Below, we derive
`Generic`, `Eq` and `Ord` implementations for all types
from `Language.Reflection.TT` and `Language.Reflection.TTImp`.

```idris
%runElab (derive1 "ModuleIdent"  [Generic', Eq', Ord'])
%runElab (derive1 "VirtualIdent" [Generic', Eq', Ord'])
%runElab (derive1 "OriginDesc"   [Generic', Eq', Ord'])
%runElab (derive1 "FC"           [Generic', Eq', Ord'])
%runElab (derive1 "NameType"     [Generic', Eq', Ord'])
%runElab (derive1 "PrimType"     [Generic', Eq', Ord'])
%runElab (derive1 "Constant"     [Generic', Eq', Ord'])
%runElab (derive1 "Namespace"    [Generic', Eq', Ord'])
%runElab (derive1 "UserName"     [Generic', Eq', Ord'])
%runElab (derive1 "Name"         [Generic', Eq', Ord'])
%runElab (derive1 "Count"        [Generic', Eq', Ord'])
%runElab (derive1 "LazyReason"   [Generic', Eq', Ord'])
%runElab (derive1 "PiInfo"       [Generic', Eq', Ord'])
%runElab (derive1 "BindMode"     [Generic', Eq', Ord'])
%runElab (derive1 "UseSide"      [Generic', Eq', Ord'])
%runElab (derive1 "DotReason"    [Generic', Eq', Ord'])
%runElab (derive1 "Visibility"   [Generic', Eq', Ord'])
%runElab (derive1 "TotalReq"     [Generic', Eq', Ord'])
%runElab (derive1 "DataOpt"      [Generic', Eq', Ord'])
%runElab (derive1 "WithFlag"     [Generic', Eq', Ord'])
%runElab (derive1 "BuiltinType"  [Generic', Eq', Ord'])
```

~~It seems not yet to be possible, to use this method in a mutual
block. Therefore, we have to write a tiny bit
of boilerplate for `Eq` and `Ord` instances
for the data types from `Language.Reflection.TTImp`~~.

I finally figured out how to derive mutually dependant implementations.
The core idea was to declare all the implementation types first,
before actually declaring the implementations. This separation has
to occur in the `Elab` monad, as can be seen in the implementation
of `deriveMutual`:

```idris
export
deriveGeneral :
     Elaboration m
  => Elaborateable t
  => List Name
  -> List (t -> TopLevel)
  -> m ()
deriveGeneral ns fs = do
  pts <- traverse (find t) ns
  let tls    := fs >>= \f => map f pts
      claims := map claim tls
      defns  := map defn tls

  declare $ claims ++ defns

%runElab deriveGeneral
  [ "TTImp"
  , "IField"
  , "IFieldUpdate"
  , "AltType"
  , "FnOpt"
  , "ITy"
  , "Data"
  , "Record"
  , "Clause"
  , "Decl"
  ] [Generic', Eq', Ord']
```

## Compiler Performance

On my machine, compiling this literate source file takes about
eight seconds. This doesn't seem too bad, considering that
we are generating instances of three type-classes
for 24 data types. The situation looks even better when
we exclude the generic instance of `TTImp`, a data type
with 29 constructors, whose `Generic`
instance alone takes about four seconds
to be derived. Indeed, when we look at the implementation of
`Generic`, we expect its compile-time complexity to grow
with the square of the number of constructors since
the generic representation of every additional constructor
results in additional layer of `S` constructors.
Considering all of the above, I am pretty happy with the
performance of the Idris compiler.

## What's next

Now that we have the means to derive some of the core interface
implementations with pretty clean syntax, let us look into
compile-time verification of these implementations.
But first, we will try and [get back some type safety](Generic5.md).

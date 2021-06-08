## Generic Deriving of Interface Implementations

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

### An Intermediary Utility Type for Generic Deriving

First, we write a utility data type holding additional
precalculated values of parameterized data types that
come up time and time again.

```idris
export
record DeriveUtil where
  constructor MkDeriveUtil

  ||| The underlying type info
  typeInfo           : ParamTypeInfo

  ||| Fully applied data type, i.e. `var "Either" .$ var "a" .$ var "b"`
  appliedType        : TTImp

  ||| The names of type parameters
  paramNames         : List Name

  ||| Types of constructor arguments where at least one
  ||| type parameter makes an appearance. These are the
  ||| `tpe` fields of `ExplicitArg` where `hasParam`
  ||| is set to true. See the documentation of `ExplicitArg`
  ||| when this is the case
  argTypesWithParams : List TTImp

private
genericUtil : ParamTypeInfo -> DeriveUtil
genericUtil ti = let pNames = map fst $ params ti
                     appTpe = appNames (name ti) pNames
                     twps   = calcArgTypesWithParams ti
                  in MkDeriveUtil ti appTpe pNames twps

export
implName : DeriveUtil -> String -> Name
implName g interfaceName =  UN $ "impl" ++ interfaceName
                                        ++ nameStr g.typeInfo.name
```

We make function `implName` for generating the name of the
implementation function available, to allow interface
implementations depending on other implementations
to access this name. This is, for instance, required in
the implemenation of `Ord'` (see below).

Since interface declarations always have the same
structure, we gather the distinct parts in a separate
data type:

```idris
export
record InterfaceImpl where
  constructor MkInterfaceImpl
  interfaceName : String
  impl          : TTImp
  type          : TTImp

public export
MkImplementation : Type
MkImplementation = DeriveUtil -> InterfaceImpl

private
implDecl : DeriveUtil -> MkImplementation -> (Decl, Decl)
implDecl g f = let (MkInterfaceImpl iname impl type) = f g
                   function = implName g iname

                in ( interfaceHint Public function type
                   , def function [var function .= impl] )
```

We are now ready to define function `derive`, which,
given the name of a data type and a list of
interface specifications (`MkImplementation`),
will derive implementations for these interfaces:

```idris
private
deriveDecls : Name -> List MkImplementation -> Elab $ List (Decl, Decl)
deriveDecls name fs = mkDecls <$> getParamInfo' name
  where mkDecls : ParamTypeInfo -> List $ (Decl, Decl)
        mkDecls pi = let g = genericUtil pi
                      in map (implDecl g) fs


export
derive : Name -> List MkImplementation -> Elab ()
derive name fs = do decls <- deriveDecls name fs
                    -- Declare types first. Then declare implementations.
                    declare $ map fst decls
                    declare $ map snd decls
```

### Instances for `Generic`, `Eq`, and `Ord`

We can now write `MkImplementation` values for `Generic`,
cleaning up parts of our code while we're at it.

```idris
private
conNames : ParamCon -> ConNames
conNames (MkParamCon con args) = let ns   = map (nameStr . name) args
                                     vars = map varStr ns
                                  in (con, ns, vars)

export
Generic' : MkImplementation
Generic' g =
  let names    = zipWithIndex (map conNames g.typeInfo.cons)
      genType  = `(Generic) .$ g.appliedType .$ mkCode g.typeInfo
      funType  = piAllImplicit  genType g.paramNames
      x        = lambdaArg "x"
      varX     = var "x"

      from    = x .=> iCase varX implicitFalse (map fromClause names)
      to      = x .=> iCase varX implicitFalse (map toClause names)
      impl    = appAll "MkGeneric" [from,to]

   in MkInterfaceImpl "Generic" impl funType
```

Before we can define `MkImplementation` functions for `Eq`
and `Ord`, we have must be able to prefix instance
declarations with the required auto implicits. For instance,
the `Eq` instance of `Maybe` has the following type:

```
{0 a: _} -> Eq a => Eq (Maybe a)
```

We define function `implementationType` to set up this type
for us:

```idris
export
implementationType : (iface : TTImp) -> DeriveUtil -> TTImp
implementationType iface (MkDeriveUtil _ appTp names argTypesWithParams) =
  let appIface = iface .$ appTp
      autoArgs = piAllAuto appIface $ map (iface .$) argTypesWithParams
   in piAllImplicit autoArgs names
```

We can now derive `Eq` implementation for data types with
a `Generic` implementation:

```idris
private
mkEq : TTImp
mkEq = varStr "MkEq" .$ `(genEq) .$ `(\a,b => not (a == b))

export
Eq' : MkImplementation
Eq' g = MkInterfaceImpl "Eq" mkEq (implementationType `(Eq) g)
```

Same for `Ord`:

```idris
private
ordFunctions : List TTImp
ordFunctions = [ `(genCompare)
               , `(\a,b => compare a b == LT)
               , `(\a,b => compare a b == GT)
               , `(\a,b => compare a b /= GT)
               , `(\a,b => compare a b /= LT)
               , `(\a,b => if compare a b == GT then a else b)
               , `(\a,b => if compare a b == LT then a else b)
               ]

export
Ord' : MkImplementation
Ord' g = let impl = appAll "MkOrd" ordFunctions
          in MkInterfaceImpl "Ord" impl (implementationType `(Ord) g)
```

### Interface Implementations for `TTImp` and Friends

Finally, lets put our new utilities to work. Below, we derive
`Generic`, `Eq` and `Ord` implementations for all types
from `Language.Reflection.TT` and `Language.Reflection.TTImp`.

```idris
%runElab (derive "ModuleIdent"  [Generic', Eq', Ord'])
%runElab (derive "VirtualIdent" [Generic', Eq', Ord'])
%runElab (derive "OriginDesc"  [Generic', Eq', Ord'])
%runElab (derive "FC"          [Generic', Eq', Ord'])
%runElab (derive "NameType"    [Generic', Eq', Ord'])
%runElab (derive "Constant"    [Generic', Eq', Ord'])
%runElab (derive "Namespace"   [Generic', Eq', Ord'])
%runElab (derive "Name"        [Generic', Eq', Ord'])
%runElab (derive "Count"       [Generic', Eq', Ord'])
%runElab (derive "LazyReason"  [Generic', Eq', Ord'])
%runElab (derive "PiInfo"      [Generic', Eq', Ord'])
%runElab (derive "BindMode"    [Generic', Eq', Ord'])
%runElab (derive "UseSide"     [Generic', Eq', Ord'])
%runElab (derive "DotReason"   [Generic', Eq', Ord'])
%runElab (derive "Visibility"  [Generic', Eq', Ord'])
%runElab (derive "TotalReq"    [Generic', Eq', Ord'])
%runElab (derive "DataOpt"     [Generic', Eq', Ord'])
```

~~It seems not yet to be possible, to use this method in a mutual
block. Therefore, we have to write a tiny bit
of boilerplate for `Eq` and `Ord` instances
for the data types from `Language.Reflection.TTImp`~~.

I finally figured out how to derive mutally dependant implementations.
The core idea was to declare all implementation types first,
before actually declaring implementations. This separation has
to occur in the `Elab` monad, as can be seen in the implementation
of `deriveMutual`:

```idris
export
deriveMutual : List (Name, List MkImplementation) -> Elab ()
deriveMutual pairs = do declss <- traverse (uncurry deriveDecls) pairs
                        -- Declare types first. Then declare implementations.
                        traverse_ (declare . map fst) declss
                        traverse_ (declare . map snd) declss

%runElab deriveMutual [ ("TTImp",        [Generic', Eq',Ord'])
                      , ("IField",       [Generic', Eq',Ord'])
                      , ("IFieldUpdate", [Generic', Eq',Ord'])
                      , ("AltType",      [Generic', Eq',Ord'])
                      , ("FnOpt",        [Generic', Eq',Ord'])
                      , ("ITy",          [Generic', Eq',Ord'])
                      , ("Data",         [Generic', Eq',Ord'])
                      , ("Record",       [Generic', Eq',Ord'])
                      , ("Clause",       [Generic', Eq',Ord'])
                      , ("Decl",         [Generic', Eq',Ord'])
                      ]
```

### Compiler Performance

On my machine, compiling this literate source file takes about
eight seconds. This doesn't seem too bad, considering that
we are generating instances of three type-classes
for 24 data types. The situation looks even better when
we exclude the generic instance of `TTImp`, a data type
with 29 constructors, whose `Generic`
instance alone takes about four seconds
to be derived. Indeed, when we look at the implementation of
`Generic`, we expect its compiletime complexity to grow
with the square of the number of constructors since
the generic representation of every additional constructor
results in additional layer of `S` constructors.
Considering all of the above, I am pretty happy with the
performance of the Idris compiler.

### What's next

Now that we have the means to derive some of the core interface
implementations with pretty clean syntax, let us look into
compile-time verification of these implementations.
But first, we will try and [get back some type safety](Generic5.md).
